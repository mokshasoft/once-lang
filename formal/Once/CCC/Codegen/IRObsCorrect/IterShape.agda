-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterShape
--
-- plan 0.119 D5: `Iter body` — THE LOOP. Its text:
--
--   load-indirect ∷ store-at-slot (suc n) ∷ c-label (ℓ o l) ∷        -- pre
--   bt ++                                                             -- the round
--   mov-to-input ∷ c-branch-tag-zero (ℓ o (suc l)) ∷ load-indirect-suc ∷
--   <⟨_,_⟩'s nine-row tail> ∷ mov-to-input ∷ c-jmp (ℓ o l) ∷          -- post14
--   c-label (ℓ o (suc l)) ∷ load-indirect-suc ∷ []                    -- post2
--
-- The round `bt` is emitted at frontier `suc⁴ n` and label base `suc² l`,
-- above the loop's own stashes and labels. This module is the shape: the
-- spans, where the two labels resolve, and the round's label and block
-- channels — `CaseShape`'s counterpart.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterShape (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in)
open import Once.CCC.Codegen.LabelRange o using (label-mono)
open import Once.CCC.Label using (module LabelId; ℓ; LabelId)
open LabelId using (idx)
open import Once.CCC.Machine.SMCore
  using (instr-ctrl; c-branch-tag-zero; c-jmp; c-label; AbstractTrace; AbstractInstr;
         load-indirect; load-indirect-suc; store-at-slot; instr-alloc-heap; mov-to-input;
         load-from-slot; store-indirect; store-indirect-suc)
open import Data.Nat.Properties using (1+n≰n)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Once.IRTy using (IRTy)
import Once.IRTy as IRT

module IterShapeC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (fl-go-skip; fl-go-shift; fl-go-prefix)
  open Resolve {FS} using (found-in-window; noLabel-outside; NoLabel; fl-hit)

  just-injL : ∀ {a b : LabelId} → just a ≡ just b → a ≡ b
  just-injL refl = refl

  module IterShape {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A)) (n l : ℕ) where

    nb lb : ℕ
    nb = proj₁ (ir-to-trace' (suc (suc (suc (suc n)))) (suc (suc l)) body)
    lb = proj₁ (proj₂ (ir-to-trace' (suc (suc (suc (suc n)))) (suc (suc l)) body))

    bt : AbstractTrace
    bt = emitted (suc (suc (suc (suc n)))) (suc (suc l)) body

    pre post14 post2 post : AbstractTrace
    pre    = load-indirect ∷ store-at-slot (suc n) ∷ instr-ctrl (c-label (ℓ o l)) ∷ []
    post14 = mov-to-input ∷ instr-ctrl (c-branch-tag-zero (ℓ o (suc l))) ∷ load-indirect-suc ∷
             store-at-slot (suc (suc n)) ∷ instr-alloc-heap 2 ∷ store-at-slot (suc (suc (suc n))) ∷
             mov-to-input ∷ load-from-slot (suc n) ∷ store-indirect ∷
             load-from-slot (suc (suc n)) ∷ store-indirect-suc ∷ load-from-slot (suc (suc (suc n))) ∷
             mov-to-input ∷ instr-ctrl (c-jmp (ℓ o l)) ∷ []
    post2  = instr-ctrl (c-label (ℓ o (suc l))) ∷ load-indirect-suc ∷ []
    post   = post14 ++ post2

    shape : emitted n l (Iter body) ≡ pre ++ bt ++ post
    shape = refl

    ------------------------------------------------------------------
    -- THE SPAN. The round sits past the three-row prologue.
    ------------------------------------------------------------------
    span-b : ∀ (prog : AbstractTrace) (base : ℕ)
           → SpanAt prog base (emitted n l (Iter body))
           → SpanAt prog (suc (suc (suc base))) bt
    span-b prog base span k i eq =
      subst (λ m → fetch prog m ≡ just i)
            (trans (cong (_+ base) (+-comm 3 k)) (+-assoc k 3 base))
            (span (suc (suc (suc k))) i (fetch-++-left bt post k i eq))

    ------------------------------------------------------------------
    -- WHERE THE TWO LABELS RESOLVE. The top `ℓ o l` is the prologue's third
    -- row; the exit `ℓ o (suc l)` sits past the prologue, the round (whose
    -- labels are at or above `suc (suc l)`) and the fourteen rows of `post14`,
    -- none of which defines a label.
    ------------------------------------------------------------------
    l≢sl : ¬ (just (ℓ o l) ≡ just (ℓ o (suc l)))
    l≢sl eq = 1+n≰n (≤-reflexive (sym (cong idx (just-injL eq))))

    noPre-e : NoLabel (ℓ o (suc l)) pre
    noPre-e = (λ ()) ∷ᴬ (λ ()) ∷ᴬ l≢sl ∷ᴬ []ᴬ

    noB-e : NoLabel (ℓ o (suc l)) bt
    noB-e = noLabel-outside (ℓ o (suc l)) bt (labels-in body (suc (suc (suc (suc n)))) (suc (suc l)))
              (λ w → 1+n≰n (proj₁ w))

    noPost14 : ∀ (m : LabelId) → NoLabel m post14
    noPost14 m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ
                 (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

    top-at done-at : ℕ
    top-at  = 2
    done-at = (3 + length bt) + 14

    top-scan : find-label (emitted n l (Iter body)) (ℓ o l) ≡ just top-at
    top-scan = fl-hit (ℓ o l) (bt ++ post) 2

    done-scan : find-label (emitted n l (Iter body)) (ℓ o (suc l)) ≡ just done-at
    done-scan =
      trans (fl-go-skip pre (bt ++ post) (ℓ o (suc l)) 0 noPre-e)
        (trans (fl-go-skip bt post (ℓ o (suc l)) 3 noB-e)
          (trans (fl-go-skip post14 post2 (ℓ o (suc l)) (3 + length bt) (noPost14 (ℓ o (suc l))))
                 (fl-hit (ℓ o (suc l)) (load-indirect-suc ∷ []) done-at)))

    top-target : ∀ (prog : AbstractTrace) (base : ℕ)
               → LabelsAt prog base (emitted n l (Iter body))
               → find-label prog (ℓ o l) ≡ just (top-at + base)
    top-target prog base la = la (ℓ o l) top-at top-scan

    done-target : ∀ (prog : AbstractTrace) (base : ℕ)
                → LabelsAt prog base (emitted n l (Iter body))
                → find-label prog (ℓ o (suc l)) ≡ just (done-at + base)
    done-target prog base la = la (ℓ o (suc l)) done-at done-scan

    ------------------------------------------------------------------
    -- THE ROUND'S CHANNELS. Its blocks are the loop's (the loop mints
    -- none); its labels resolve past the prologue, whose one label `ℓ o l`
    -- is below the round's window.
    ------------------------------------------------------------------
    blocks-b : ∀ (prog : AbstractTrace) → BlocksAt prog (blocks n l (Iter body))
             → BlocksAt prog (blocks (suc (suc (suc (suc n)))) (suc (suc l)) body)
    blocks-b prog bl = bl

    labels-b : ∀ (prog : AbstractTrace) (base : ℕ)
             → LabelsAt prog base (emitted n l (Iter body))
             → LabelsAt prog (suc (suc (suc base))) bt
    labels-b prog base la m j eq =
      subst (λ z → find-label prog m ≡ just z) (+-assoc j 3 base) (la m (j + 3) scan)
      where
        inW : (suc (suc l) ≤ idx m) × (idx m < lb)
        inW = found-in-window bt m j eq (labels-in body (suc (suc (suc (suc n)))) (suc (suc l)))

        noPre-m : NoLabel m pre
        noPre-m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ
                  (λ e → 1+n≰n (≤-trans (n≤1+n (suc l)) (≤-trans (proj₁ inW) (≤-reflexive (sym (cong idx (just-injL e))))))) ∷ᴬ []ᴬ

        scan : find-label (emitted n l (Iter body)) m ≡ just (j + 3)
        scan = trans (fl-go-skip pre (bt ++ post) m 0 noPre-m)
                     (fl-go-prefix bt post m 3 (j + 3)
                        (trans (fl-go-shift bt m 3 0) (cong (mmap (_+ 3)) eq)))
