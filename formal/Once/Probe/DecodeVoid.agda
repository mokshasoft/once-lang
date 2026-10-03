-- PROBE (plan 0.105 §g): `SMCore.decode-unread : IsBaseType A → StoredValue →
-- ⟦ A ⟧` gave `⊥` once an interpretation was inhabited:
--   decode-void : ⊥
--   decode-void = decode-unread base-Void unit-storedvalue
-- The argument is now decoded from memory and may fail; at `Void` it does.
module Once.Probe.DecodeVoid where

open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Functor.Translate using (base-Void)
open import Once.Denotation.TraceMonad using (no-world)
open import Once.CCC.Target.RiscV64.FrameInstantiation using (rv64-frame-semantics)
open import Once.CCC.Machine.SMCore using (module AbstractExec; LocState)
open AbstractExec {rv64-frame-semantics no-world} using (decode-at; unit-storedvalue)

decode-void : ∀ (s : LocState _) → decode-at base-Void unit-storedvalue s ≡ nothing
decode-void s = refl
