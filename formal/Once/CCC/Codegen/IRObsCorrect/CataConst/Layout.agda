-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Layout   (plan 0.135 S3, cata M1)
--
-- WHERE THE PARTS OF A `strat-const` CATA SIT. Its text is
--
--     setup (13) ++ call (15) ++ c-jmp end ∷ c-thunk body bb ∷ at ++ c-ret bb ∷ c-label end ∷ []
--
-- (`cata-trace-const`), with the algebra `at` emitted ONCE at frontier 0 and
-- called through the closure record the setup builds. This module reads the
-- cata's three placement premises (`SpanAt`, `LabelsAt`, and the block
-- channel, which is the algebra's own) down to what the run needs: the
-- fetches of the straight rows and the two control rows, the algebra's body
-- block where the call lands, the body's own label resolution, and where the
-- jump over the body goes.
--
-- The 30-row prefix defines no `c-label` (it is straight code, a jump and a
-- marker), so a label the body resolves is resolved 30 rows further on in
-- the cata, and the end label is outside the algebra's label window.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataConst.Layout (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRToTrace o
  using (rec-count; cata-strategy; CataStrategy; strat-const; cata-dispatch; cata-call-setup; cata-call; cata-body)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractTrace; instr-ctrl; c-jmp; c-label; c-ret; c-thunk; block-layout)
open import Once.CCC.Label using (ℓ; LabelId)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F)
import Once.IRTy as IRTy′
import Data.Nat as ℕ
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

-- the end pc, as arithmetic
end-pc : ∀ (a b : ℕ) → suc ((31 + a) + b) ≡ (30 + (a + 2)) + b
end-pc = solve 2 (λ a b → con 1 :+ ((con 31 :+ a) :+ b) := (con 30 :+ (a :+ con 2)) :+ b) refl

-- The classifier's `strat-const` is "no recursive position".
const-rc : ∀ G → cata-strategy G ≡ strat-const → rec-count G ≡ 0
const-rc G eq with rec-count G | eq
... | zero  | _  = refl
... | suc _ | ()

module CataLayoutC {FS : FrameSemantics} where

  open Core {FS}
  open ResuspBaseC {FS} using (span-take; span-drop; labels-take; labels-drop)
  open Resolve {FS} using (NoLabel; noLabel-outside; fl-hit)
  open FlatStepsAPI {FS} using (fl-go-skip)

  module Text {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C) (n l : ℕ) where

    bb l1 : ℕ
    bb = proj₁ (ir-to-trace' 0 l alg)
    l1 = proj₁ (proj₂ (ir-to-trace' 0 l alg))

    at : AbstractTrace
    at = emitted 0 l alg

    endL : LabelId
    endL = ℓ o (l1 ℕ.+ 1)

    setup call post pre29 pre30 text : AbstractTrace
    setup = cata-call-setup n (n ℕ.+ 1) (n ℕ.+ 2) l1
    call  = cata-call n (n ℕ.+ 1) (n ℕ.+ 2) (n ℕ.+ 3)
    post  = instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label endL) ∷ []
    pre29 = setup ++ (call ++ instr-ctrl (c-jmp endL) ∷ [])
    pre30 = setup ++ (call ++ instr-ctrl (c-jmp endL) ∷ instr-ctrl (c-thunk (ℓ o l1) bb) ∷ [])
    text  = setup ++ (call ++ cata-body l1 (l1 ℕ.+ 1) bb at)

    -- `ir-to-trace'`'s dispatch, at the strategy this case is about
    emitted-eq : cata-strategy ⌈ F ⌉F ≡ strat-const → emitted n l (Cata wf alg) ≡ text
    emitted-eq eq = cong (λ st → proj₂ (proj₂ (cata-dispatch st bb n l1 at))) eq

    len-text : length text ≡ 30 + (length at + 2)
    len-text = cong (30 +_) (length-++ at {post})

    -- the end label is above the algebra's window `[l , l1)`
    no-end : NoLabel endL at
    no-end = noLabel-outside endL at (labels-in alg 0 l)
               (λ w → <-irrefl refl (<-≤-trans (proj₂ w) (m≤m+n l1 1)))

    -- the prefix defines no label
    no-pre : ∀ m → NoLabel m pre30
    no-pre m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ
               (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ
               (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ
               (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

    end-scan : find-label text endL ≡ just (31 + length at)
    end-scan = trans (fl-go-skip at post endL 30 no-end) (fl-hit endL [] (suc (30 + length at)))

    ------------------------------------------------------------------
    -- …and in the program.
    ------------------------------------------------------------------
    module At (prog : AbstractTrace) (base : ℕ) (span : SpanAt prog base text) (la : LabelsAt prog base text) where

      span-setup : SpanAt prog base setup
      span-setup = span-take prog setup base span

      span-call : SpanAt prog (13 + base) call
      span-call = span-take prog call (13 + base) (span-drop prog setup base span)

      fetch-jmp : fetch prog (28 + base) ≡ just (instr-ctrl (c-jmp endL))
      fetch-jmp = span 28 _ refl

      fetch-thunk : fetch prog (29 + base) ≡ just (instr-ctrl (c-thunk (ℓ o l1) bb))
      fetch-thunk = span 29 _ refl

      fetch-end : fetch prog ((31 + length at) + base) ≡ just (instr-ctrl (c-label endL))
      fetch-end = span (31 + length at) _
                    (subst (λ z → fetch (at ++ post) z ≡ just (instr-ctrl (c-label endL)))
                           (+-comm (length at) 1) (fetch-++-right at post 1))

      body-span : SpanAt prog (29 + base) (block-layout (ℓ o l1 , bb , at))
      body-span = span-take prog (block-layout (ℓ o l1 , bb , at)) {instr-ctrl (c-label endL) ∷ []} (29 + base)
                    (subst (λ t → SpanAt prog (29 + base) (instr-ctrl (c-thunk (ℓ o l1) bb) ∷ t))
                           (sym (++-assoc at (instr-ctrl (c-ret bb) ∷ []) (instr-ctrl (c-label endL) ∷ [])))
                           (span-drop prog pre29 base span))

      body-labels : LabelsAt prog (30 + base) at
      body-labels = labels-take prog at {post} (30 + base)
                      (labels-drop prog pre30 {at ++ post} base la (λ m _ _ → no-pre m))

      end-label : find-label prog endL ≡ just ((31 + length at) + base)
      end-label = la endL (31 + length at) end-scan
