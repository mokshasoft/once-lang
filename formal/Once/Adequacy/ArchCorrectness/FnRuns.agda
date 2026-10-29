-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FnRuns — plan 0.125 S3: THE PROGRAM'S
-- FUNCTIONS RUN AS THE TABLE SAYS (`FnRuns`, discharged).
--
-- An entry's meaning is its body in the environment of the entries AFTER it
-- (`tableEnv-at`), and the table is a telescope (`TeleLinked`): each body is
-- linked in its suffix. So the induction runs from the table's end. For
-- `e ∷ es`, a call naming `e` runs `e`'s body, which is correct at the
-- definition `fname e` and table `es` (`ir-obs-correct` there), entered from
-- the call (`fn-call`, the block-call lemma at an `e-fn` marker); its own
-- calls are into `es`, which the induction already discharged. A call naming
-- another entry is the suffix's. The value relation is table-free
-- (`ValueRel`), so the caller and the callee state one input and one result.
--
-- What the image owes is per entry (`EntryAt`): the call scan finds its
-- marker, its unit spans there, and its labels and blocks resolve.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.FnRuns where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Maybe using (just)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Name using (CanonicalName)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.IRTy using (_≟IRTy_)
open import Once.Denotation.Program
  using (IRFun; LinkedAt; LinkedAt-at; TeleLinked; NamesDistinct; tableCalls; tableEnv-at)
open Once.Denotation.Program.IRFun using (fname; fdom; fcod; fbody)
open import Once.CCC.FrameSemantics using (FrameSemantics)
import Once.CCC.FrameSemantics
import Once.Internal.Trace as TM
open import Once.CCC.Machine.SMCore using (AbstractTrace; e-fn)
import Once.CCC.Codegen.IRToTrace as IT
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot)
import Once.CCC.Codegen.IRObsCorrect.Interface as Iface
import Once.CCC.Codegen.IRObsCorrect.BlockCall as BCall
import Once.CCC.Codegen.IRObsCorrectFlat as IOF

module FnRunsC {FS : FrameSemantics} where

  σ = TM.Interp.sig (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS)

  open FlatMachine {FS} using (find-fn)
  open CataNextSlot {FS} using (AllSlotStable)

  -- What the image owes one entry: its unit, placed at label counter `lab`
  -- and marker `ent`, spans there behind its marker, the call scan finds it,
  -- and its labels and blocks resolve where they sit.
  record EntryAt (prog : AbstractTrace) (e : IRFun) : Set where
    field
      lab    : ℕ
      ent    : ℕ
      found  : find-fn prog (fname e) ≡ just ent
      span   : Iface.Core.SpanAt (fname e) [] {FS} prog ent
                 (BCall.BlockCallC.entry-layout (fname e) [] {FS} (e-fn (fname e))
                    (IT.ir-stack-budget-from (fname e) lab (fbody e))
                    (Iface.Core.emitted (fname e) [] {FS} 0 lab (fbody e)))
      labels : Iface.Core.LabelsAt (fname e) [] {FS} prog (suc ent) (Iface.Core.emitted (fname e) [] {FS} 0 lab (fbody e))
      blks   : Iface.Core.BlocksAt (fname e) [] {FS} prog (Iface.Core.blocks (fname e) [] {FS} 0 lab (fbody e))

  -- The induction. `FnRuns` does not depend on the definition name it is read
  -- at (`o′`): everything it mentions is table-free or names the table.
  fn-runs : ∀ (prog : AbstractTrace) → AllSlotStable prog
          → (es : List IRFun) → TeleLinked σ es → All (EntryAt prog) es
          → ∀ (o′ : CanonicalName) → Iface.Core.FnRuns o′ es {FS} prog
  fn-runs prog ss []       _          _          o′ f A B ()
  fn-runs prog ss (e ∷ es) (le , tl) (ea ∷ eas) o′ f A B lk =
    go (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) lk
    where
      ih : Iface.Core.FnRuns (fname e) es {FS} prog
      ih = fn-runs prog ss es tl eas (fname e)

      open EntryAt ea

      go : ∀ (d₁ : Dec (fname e ≡ f)) (d₂ : Dec (fdom e ≡ A)) (d₃ : Dec (fcod e ≡ B))
         → LinkedAt-at e es f A B d₁ d₂ d₃
         → Iface.Core.FnRunsAt o′ (e ∷ es) {FS} prog f A B
             (tableEnv-at (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS)) e es f A B d₁ d₂ d₃)
      go (yes refl) (yes refl) (yes refl) _ =
        ent , found ,
        BCall.BlockCallC.fn-call (fname e) es {FS} (fbody e)
          (IOF.IRObsCorrectFlatness.ir-obs-correct (fname e) es {FS} (fbody e) le)
          lab prog (e-fn (fname e)) (IT.ir-stack-budget-from (fname e) lab (fbody e)) ent ss
          (record { functions = ih }) span blks labels
      go (yes refl) (yes refl) (no _) l = ih f A B l
      go (yes refl) (no _)     _      l = ih f A B l
      go (no _)     _          _      l = ih f A B l
