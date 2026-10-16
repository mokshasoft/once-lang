{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- POC 0.120-B′ — the trace of a computation against a world.
--
-- Each call of a block is one visible step; the end of a block is one silent
-- step; a returned value or a halting call ends the trace. Mutually
-- corecursive: the trace (`Tr`) and the delay of its next step (`Delay`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; Event; eventOf; call; module Op; BTy)

module POC0120.TraceOf (Σ : Signature) where

open import Data.List using (_++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open Op using (ans)
open import Once.Spec.Effect Σ using (T; roll; done; node; T∞; module T∞)
open import Once.Spec.Observation Σ using (Interp; module Interp; History; resume)
open import Once.Spec.Delay using (Delay; module Delay)
open import POC0120.Traces Event using (Tr; module Tr; End; returned; halted)
open T∞ using (force)
open Tr using (next)
open Delay using (step)

module _ (ι : Interp) where
  open Interp ι using (answer)

  trace  : ∀ {X} → History → T∞ X → Tr X
  blockD : ∀ {X} → History → T (X ⊎ T∞ X) → Delay (End X ⊎ (Event × Tr X))
  restOf : ∀ {X} → History → Maybe (T (X ⊎ T∞ X)) → Tr X

  next (trace h m) = blockD h (force m)
  step (blockD h (roll (done (inj₁ x))))     = inj₁ (inj₁ (returned x))
  step (blockD h (roll (done (inj₂ m))))     = inj₂ (blockD h (force m))
  step (blockD h (roll (node (call o a k)))) =
    inj₁ (inj₂ (eventOf o a , restOf (h ++ [ eventOf o a ]) (resume (ans o) (answer o h a) k)))
  next (restOf h nothing)  = record { step = inj₁ (inj₁ halted) }
  next (restOf h (just t)) = blockD h t
