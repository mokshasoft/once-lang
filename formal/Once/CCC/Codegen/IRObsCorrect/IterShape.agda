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
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (get; get-i; get-one; get-i-P; put; put-All)
open import Once.CCC.Codegen.IRObsCorrect.Pair.Build o tbl using (module PairBuildC)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All-++⁺)
open import Data.Nat using (_⊔_)

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

    -- plan 0.123 B.4 α: the continuation rebuilds `(e , a′)` with `Pair.Build`'s
    -- tail; each read (`e`, `a′`, the result) is `get`'s one instruction
    T : AbstractTrace
    T = PairBuildC.tail-text {FS} n E A

    pre post14 post2 post : AbstractTrace
    pre    = get-i E 0 ∷ store-at-slot (suc n) ∷ instr-ctrl (c-label (ℓ o l)) ∷ []
    post14 = mov-to-input ∷ instr-ctrl (c-branch-tag-zero (ℓ o (suc l))) ∷ get-i A 1 ∷
             (T ++ mov-to-input ∷ instr-ctrl (c-jmp (ℓ o l)) ∷ [])
    post2  = instr-ctrl (c-label (ℓ o (suc l))) ∷ get-i B 1 ∷ []
    post   = post14 ++ post2

    E′ : AbstractTrace
    E′ = pre ++ bt ++ post

    shape : emitted n l (Iter body) ≡ E′
    shape =
      trans (cong (λ x → x ++ G) (get-one E 0))
     (trans (cong (λ y → get-i E 0 ∷ store-at-slot (suc n) ∷ instr-ctrl (c-label (ℓ o l)) ∷
                         (bt ++ mov-to-input ∷ instr-ctrl (c-branch-tag-zero (ℓ o (suc l))) ∷ (y ++ H)))
                  (get-one A 1))
     (trans (cong (λ z → get-i E 0 ∷ store-at-slot (suc n) ∷ instr-ctrl (c-label (ℓ o l)) ∷
                         (bt ++ mov-to-input ∷ instr-ctrl (c-branch-tag-zero (ℓ o (suc l))) ∷ get-i A 1 ∷
                          (store-at-slot (suc (suc n)) ∷ instr-alloc-heap (2 ⊔ size (E IRT.* A)) ∷
                           store-at-slot (suc (suc (suc n))) ∷ (P ++ Q ++ (L3 ∷ R3 ++ z)))))
                  (get-one B 1))
            (cong (λ t → get-i E 0 ∷ store-at-slot (suc n) ∷ instr-ctrl (c-label (ℓ o l)) ∷
                         (bt ++ mov-to-input ∷ instr-ctrl (c-branch-tag-zero (ℓ o (suc l))) ∷ get-i A 1 ∷
                          (store-at-slot (suc (suc n)) ∷ instr-alloc-heap (2 ⊔ size (E IRT.* A)) ∷
                           store-at-slot (suc (suc (suc n))) ∷ t)))
                  (sym X))))
      where
        P = put E (suc n) (suc (suc (suc n))) 0
        Q = put A (suc (suc n)) (suc (suc (suc n))) (size E)
        L3 = load-from-slot (suc (suc (suc n)))
        R3 = mov-to-input ∷ instr-ctrl (c-jmp (ℓ o l)) ∷ instr-ctrl (c-label (ℓ o (suc l))) ∷ []
        H = store-at-slot (suc (suc n)) ∷ instr-alloc-heap (2 ⊔ size (E IRT.* A)) ∷ store-at-slot (suc (suc (suc n))) ∷
            (P ++ Q ++ (L3 ∷ R3 ++ get B 1))
        G = store-at-slot (suc n) ∷ instr-ctrl (c-label (ℓ o l)) ∷
            (bt ++ mov-to-input ∷ instr-ctrl (c-branch-tag-zero (ℓ o (suc l))) ∷ (get A 1 ++ H))
        R4 = mov-to-input ∷ instr-ctrl (c-jmp (ℓ o l)) ∷ instr-ctrl (c-label (ℓ o (suc l))) ∷ get-i B 1 ∷ []
        -- the tail's own `++`s, reassociated
        X : ((P ++ (Q ++ L3 ∷ [])) ++ mov-to-input ∷ instr-ctrl (c-jmp (ℓ o l)) ∷ []) ++ post2
          ≡ P ++ (Q ++ (L3 ∷ R4))
        X = trans (++-assoc (P ++ (Q ++ L3 ∷ [])) (mov-to-input ∷ instr-ctrl (c-jmp (ℓ o l)) ∷ []) post2)
           (trans (++-assoc P (Q ++ L3 ∷ []) R4)
                  (cong (P ++_) (++-assoc Q (L3 ∷ []) R4)))

    -- the obligation's text, read as `E′`
    span′ : ∀ {prog : AbstractTrace} {base : ℕ} → SpanAt prog base (emitted n l (Iter body)) → SpanAt prog base E′
    span′ {prog} {base} = subst (SpanAt prog base) shape

    la′ : ∀ {prog : AbstractTrace} {base : ℕ} → LabelsAt prog base (emitted n l (Iter body)) → LabelsAt prog base E′
    la′ {prog} {base} = subst (LabelsAt prog base) shape

    ------------------------------------------------------------------
    -- THE SPAN. The round sits past the three-row prologue.
    ------------------------------------------------------------------
    span-b : ∀ (prog : AbstractTrace) (base : ℕ)
           → SpanAt prog base (emitted n l (Iter body))
           → SpanAt prog (suc (suc (suc base))) bt
    span-b prog base span k i eq =
      subst (λ m → fetch prog m ≡ just i)
            (trans (cong (_+ base) (+-comm 3 k)) (+-assoc k 3 base))
            (span′ {prog} {base} span (suc (suc (suc k))) i (fetch-++-left bt post k i eq))

    ------------------------------------------------------------------
    -- WHERE THE TWO LABELS RESOLVE. The top `ℓ o l` is the prologue's third
    -- row; the exit `ℓ o (suc l)` sits past the prologue, the round (whose
    -- labels are at or above `suc (suc l)`) and the fourteen rows of `post14`,
    -- none of which defines a label.
    ------------------------------------------------------------------
    l≢sl : ¬ (just (ℓ o l) ≡ just (ℓ o (suc l)))
    l≢sl eq = 1+n≰n (≤-reflexive (sym (cong idx (just-injL eq))))

    -- a read defines no label
    get-nodef : ∀ (X : IRTy) k (m : LabelId) → ¬ (label-of? (get-i X k) ≡ just m)
    get-nodef X k m = get-i-P {λ i → ¬ (label-of? i ≡ just m)} X k (λ _ ()) (λ _ ()) (λ ())

    get-nothing : ∀ (X : IRTy) k → label-of? (get-i X k) ≡ nothing
    get-nothing X k = get-i-P {λ i → label-of? i ≡ nothing} X k (λ _ → refl) (λ _ → refl) refl

    noPre-e : NoLabel (ℓ o (suc l)) pre
    noPre-e = get-nodef E 0 (ℓ o (suc l)) ∷ᴬ (λ ()) ∷ᴬ l≢sl ∷ᴬ []ᴬ

    noB-e : NoLabel (ℓ o (suc l)) bt
    noB-e = noLabel-outside (ℓ o (suc l)) bt (labels-in body (suc (suc (suc (suc n)))) (suc (suc l)))
              (λ w → 1+n≰n (proj₁ w))

    -- the tail is labels-free (its puts too)
    noT : ∀ (m : LabelId) → NoLabel m T
    noT m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ
            All-++⁺ (put-All {λ i → ¬ (label-of? i ≡ just m)} E (suc n) (suc (suc (suc n))) 0 (λ ()) (λ ()) (λ ()) (λ _ ()) (λ _ ()))
                    (All-++⁺ (put-All {λ i → ¬ (label-of? i ≡ just m)} A (suc (suc n)) (suc (suc (suc n))) (size E) (λ ()) (λ ()) (λ ()) (λ _ ()) (λ _ ()))
                             ((λ ()) ∷ᴬ []ᴬ))

    noPost14 : ∀ (m : LabelId) → NoLabel m post14
    noPost14 m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ get-nodef A 1 m ∷ᴬ All-++⁺ (noT m) ((λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ)

    top-at done-at : ℕ
    top-at  = 2
    done-at = (3 + length bt) + length post14

    -- the prologue's read defines no label, so a scan walks past it
    pre-go : ∀ (m : LabelId) → find-label E′ m ≡ fl-go (store-at-slot (suc n) ∷ instr-ctrl (c-label (ℓ o l)) ∷ (bt ++ post)) m 1
    pre-go m = cong (λ z → fl-at z (store-at-slot (suc n) ∷ instr-ctrl (c-label (ℓ o l)) ∷ (bt ++ post)) m 0) (get-nothing E 0)

    top-scan : find-label E′ (ℓ o l) ≡ just top-at
    top-scan = trans (pre-go (ℓ o l)) (fl-hit (ℓ o l) (bt ++ post) 2)

    done-scan : find-label E′ (ℓ o (suc l)) ≡ just done-at
    done-scan =
      trans (fl-go-skip pre (bt ++ post) (ℓ o (suc l)) 0 noPre-e)
        (trans (fl-go-skip bt post (ℓ o (suc l)) 3 noB-e)
          (trans (fl-go-skip post14 post2 (ℓ o (suc l)) (3 + length bt) (noPost14 (ℓ o (suc l))))
                 (fl-hit (ℓ o (suc l)) (get-i B 1 ∷ []) done-at)))

    top-target : ∀ (prog : AbstractTrace) (base : ℕ)
               → LabelsAt prog base (emitted n l (Iter body))
               → find-label prog (ℓ o l) ≡ just (top-at + base)
    top-target prog base la = la′ {prog} {base} la (ℓ o l) top-at top-scan

    done-target : ∀ (prog : AbstractTrace) (base : ℕ)
                → LabelsAt prog base (emitted n l (Iter body))
                → find-label prog (ℓ o (suc l)) ≡ just (done-at + base)
    done-target prog base la = la′ {prog} {base} la (ℓ o (suc l)) done-at done-scan

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
      subst (λ z → find-label prog m ≡ just z) (+-assoc j 3 base) (la′ {prog} {base} la m (j + 3) scan)
      where
        inW : (suc (suc l) ≤ idx m) × (idx m < lb)
        inW = found-in-window bt m j eq (labels-in body (suc (suc (suc (suc n)))) (suc (suc l)))

        noPre-m : NoLabel m pre
        noPre-m = get-nodef E 0 m ∷ᴬ (λ ()) ∷ᴬ
                  (λ e → 1+n≰n (≤-trans (n≤1+n (suc l)) (≤-trans (proj₁ inW) (≤-reflexive (sym (cong idx (just-injL e))))))) ∷ᴬ []ᴬ

        scan : find-label E′ m ≡ just (j + 3)
        scan = trans (fl-go-skip pre (bt ++ post) m 0 noPre-m)
                     (fl-go-prefix bt post m 3 (j + 3)
                        (trans (fl-go-shift bt m 3 0) (cong (mmap (_+ 3)) eq)))
