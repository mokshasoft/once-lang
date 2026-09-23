-- PROBE (not part of the build): is `CalleeRun.live` a definitional read-back
-- through the three state transformers on the callee's path?
module Once.Probe.LiveReadback where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (halted)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module P {FS : FrameSemantics} where
  open FlatMachine {FS}

  -- (1) RELOCATION is transparent for `halted`: `shift` touches only
  --     fpc / fret / flink.
  halted-shift : ∀ (d : ℕ) (fs : FlatState)
               → halted (floc (shift d fs)) ≡ halted (floc fs)
  halted-shift d fs = refl

  -- (2) The BLOCK PROLOGUE is transparent: `do-thunk` rewrites `floc`, but
  --     only its `stackMem` field.
  halted-thunk : ∀ (b : ℕ) (fs : FlatState)
               → halted (floc (do-thunk b fs)) ≡ halted (floc fs)
  halted-thunk b fs = refl

  -- (3) The RETURN is transparent ONLY on a non-empty return stack.
  halted-ret-∷ : ∀ (rpc : ℕ) (rest : List ℕ) (fs : FlatState)
               → halted (floc (do-ret (rpc ∷ rest) fs)) ≡ halted (floc fs)
  halted-ret-∷ rpc rest fs = refl

  -- …and on an EMPTY one it is `true` — the call would come back halted.
  halted-ret-[] : ∀ (fs : FlatState)
                → halted (floc (do-ret [] fs)) ≡ true
  halted-ret-[] fs = refl

  -- The aux-style read-back a consumer can actually rewrite with (the
  -- `do-ret-*` family's missing member).
  do-ret-halted : ∀ (fs : FlatState) (rpc : ℕ) (rest : List ℕ)
                → fret fs ≡ rpc ∷ rest
                → halted (floc (do-ret (fret fs) fs)) ≡ halted (floc fs)
  do-ret-halted fs rpc rest e rewrite e = refl
