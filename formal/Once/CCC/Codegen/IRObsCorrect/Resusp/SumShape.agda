-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.SumShape
--
-- plan 0.135 S3: the SHAPE of a sum layer's re-suspension
-- (`resuspend-layer … (wf-Sum wfF wfG)`), the same flat-control skeleton
-- `case` emits:
--
--   pre   = store-at-slot n ∷ restore-input n ∷ c-branch-tag-zero (ℓ l) ∷
--           restore-input n ∷ load-indirect-suc ∷ []
--   armG  = tG ++ tail9 1
--   midJ  = c-jmp (ℓ (suc l)) ∷ c-label (ℓ l) ∷ restore-input n ∷ load-indirect-suc ∷ []
--   armF  = tF ++ tail9 0
--   post  = c-label (ℓ (suc l)) ∷ []
--
-- (`tF` is emitted first, two labels up; `tG` continues from its outputs —
-- text order `G`-then-`F`, as in `case`.) Here: where each part sits, where
-- the two jumps land, and the two end pcs.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.SumShape (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl
open import Once.CCC.Codegen.IRToTrace o using (resuspend-layer)
open import Once.CCC.Codegen.LabelScope o using (resuspend-labels-in)
open import Once.CCC.Codegen.LabelRange o using (resuspend-label-mono)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; li-none; li-lab)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-branch-tag-zero; c-jmp; c-label
        ; store-at-slot; restore-input; load-from-slot; load-indirect-suc; store-indirect
        ; store-indirect-suc; mov-to-input; instr-alloc-heap; instr-load-tag-lit)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ; LabelId; module LabelId)
open LabelId using (idx)
open import Once.IRTy using (IRFunctor; WellFormedFI; wf-Sum)
open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (1+n≰n)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

-- the arithmetic, hoisted out of every telescope
sum-shift-l : ∀ (a b : ℕ) → 4 + (a + (5 + b)) ≡ 3 + (suc (5 + a) + b)
sum-shift-l = solve 2 (λ a b → con 4 :+ (a :+ (con 5 :+ b)) := con 3 :+ ((con 1 :+ (con 5 :+ a)) :+ b)) refl

sum-lab : ∀ (a b : ℕ) → 1 + (a + (5 + b)) ≡ suc (5 + a) + b
sum-lab = solve 2 (λ a b → con 1 :+ (a :+ (con 5 :+ b)) := (con 1 :+ (con 5 :+ a)) :+ b) refl

sum-join : ∀ (a f b : ℕ) → (((5 + a) + 4) + f) + b ≡ f + (4 + (a + (5 + b)))
sum-join = solve 3 (λ a f b → (((con 5 :+ a) :+ con 4) :+ f) :+ b := f :+ (con 4 :+ (a :+ (con 5 :+ b)))) refl

sum-end-r : ∀ (a f b : ℕ) → suc ((((5 + a) + 4) + f) + b) ≡ (5 + (a + (4 + (f + 1)))) + b
sum-end-r = solve 3 (λ a f b → con 1 :+ ((((con 5 :+ a) :+ con 4) :+ f) :+ b)
                            := (con 5 :+ (a :+ (con 4 :+ (f :+ con 1)))) :+ b) refl

sum-end-l : ∀ (a t b : ℕ) → suc (9 + (t + (3 + (suc (5 + a) + b)))) ≡ (5 + (a + (4 + ((t + 9) + 1)))) + b
sum-end-l = solve 3 (λ a t b → con 1 :+ (con 9 :+ (t :+ (con 3 :+ ((con 1 :+ (con 5 :+ a)) :+ b))))
                            := (con 5 :+ (a :+ (con 4 :+ ((t :+ con 9) :+ con 1)))) :+ b) refl

module ResuspSumShapeC {FS : FrameSemantics} where

  open Core {FS}
  open ResuspBaseC {FS}
  open FlatStepsAPI {FS} using (fl-go-skip)
  open Resolve {FS} using (NoLabel; found-in-window; noLabel-outside; fl-hit)

  just-injL : ∀ {a b : LabelId} → just a ≡ just b → a ≡ b
  just-injL refl = refl

  module SumShape (lbl-n : ℕ) {G₁ G₂ : IRFunctor} (wF : WellFormedFI G₁) (wG : WellFormedFI G₂) (n l : ℕ) where

    lbl : LabelId
    lbl = ℓ o lbl-n

    dst tmp nF : ℕ
    dst = suc n
    tmp = suc dst
    nF  = suc tmp

    n2 l2 l3 : ℕ
    n2 = proj₁ (resuspend-layer nF (suc (suc l)) lbl 0 wF)
    l2 = proj₁ (proj₂ (resuspend-layer nF (suc (suc l)) lbl 0 wF))
    l3 = proj₁ (proj₂ (resuspend-layer n2 l2 lbl 0 wG))

    tail9 : ℕ → AbstractTrace
    tail9 tag = store-at-slot tmp ∷ instr-alloc-heap 2 ∷ store-at-slot dst ∷ mov-to-input ∷
                load-from-slot tmp ∷ store-indirect-suc ∷ instr-load-tag-lit tag ∷ store-indirect ∷
                load-from-slot dst ∷ []

    tF tG pre armG midJ armF post X1 : AbstractTrace
    tF   = proj₂ (proj₂ (resuspend-layer nF (suc (suc l)) lbl 0 wF))
    tG   = proj₂ (proj₂ (resuspend-layer n2 l2 lbl 0 wG))
    pre  = store-at-slot n ∷ restore-input n ∷ instr-ctrl (c-branch-tag-zero (ℓ o l)) ∷
           restore-input n ∷ load-indirect-suc ∷ []
    armG = tG ++ tail9 1
    midJ = instr-ctrl (c-jmp (ℓ o (suc l))) ∷ instr-ctrl (c-label (ℓ o l)) ∷ restore-input n ∷ load-indirect-suc ∷ []
    armF = tF ++ tail9 0
    post = instr-ctrl (c-label (ℓ o (suc l))) ∷ []
    X1   = midJ ++ (armF ++ post)

    trace : AbstractTrace
    trace = proj₂ (proj₂ (resuspend-layer n l lbl 0 (wf-Sum wF wG)))

    shape : trace ≡ pre ++ (armG ++ X1)
    shape = refl

    len : length trace ≡ 5 + (length armG + (4 + (length armF + 1)))
    len = cong (5 +_) (trans (length-++ armG {X1}) (cong (λ z → length armG + (4 + z)) (length-++ armF {post})))

    lenF : length armF ≡ length tF + 9
    lenF = length-++ tF {tail9 0}

    ------------------------------------------------------------------
    -- LABEL WINDOWS.
    ------------------------------------------------------------------
    ssl≤l2 : suc (suc l) ≤ l2
    ssl≤l2 = resuspend-label-mono nF (suc (suc l)) lbl 0 wF

    li9 : ∀ {lo hi} (tag : ℕ) → LabelsIn lo hi (tail9 tag)
    li9 tag = li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
              li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ []ᴬ

    liArmG : LabelsIn l2 l3 armG
    liArmG = ++⁺ (resuspend-labels-in l2 l3 n2 l2 lbl 0 wG ≤-refl ≤-refl) (li9 1)

    liArmF : LabelsIn (suc (suc l)) l2 armF
    liArmF = ++⁺ (resuspend-labels-in (suc (suc l)) l2 nF (suc (suc l)) lbl 0 wF ≤-refl ≤-refl) (li9 0)

    sl<l2 : suc l < l2
    sl<l2 = ssl≤l2
    l<l2 : l < l2
    l<l2 = ≤-trans (n≤1+n (suc l)) ssl≤l2

    -- armF ++ post resolves in [suc l, l2)
    liFP : LabelsIn (suc l) l2 (armF ++ post)
    liFP = ++⁺ (++⁺ (resuspend-labels-in (suc l) l2 nF (suc (suc l)) lbl 0 wF (n≤1+n (suc l)) ≤-refl) (li9 0))
               (li-lab refl ≤-refl sl<l2 ∷ᴬ []ᴬ)

    -- X1 resolves in [l, l2)
    liX1 : LabelsIn l l2 X1
    liX1 = li-lab refl (n≤1+n l) sl<l2 ∷ᴬ li-lab refl ≤-refl l<l2 ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
           ++⁺ (++⁺ (resuspend-labels-in l l2 nF (suc (suc l)) lbl 0 wF (≤-trans (n≤1+n l) (n≤1+n (suc l))) ≤-refl) (li9 0))
               (li-lab refl (n≤1+n l) sl<l2 ∷ᴬ []ᴬ)

    nolab-pre : ∀ m → NoLabel m pre
    nolab-pre m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

    -- the mid row defines `ℓ l` only
    nolab-mid : ∀ m → suc l ≤ idx m → NoLabel m midJ
    nolab-mid m h = (λ ()) ∷ᴬ (λ eq → 1+n≰n (subst (suc l ≤_) (sym (cong idx (just-injL eq))) h))
                  ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

    noG : ∀ m → idx m < l2 → NoLabel m armG
    noG m h = noLabel-outside m armG liArmG (λ w → 1+n≰n (≤-trans h (proj₁ w)))

    ------------------------------------------------------------------
    -- THE TWO JUMP TARGETS.
    ------------------------------------------------------------------
    P₀ J₀ : ℕ
    P₀ = suc (5 + length armG)
    J₀ = ((5 + length armG) + 4) + length armF

    inl-scan : find-label trace (ℓ o l) ≡ just P₀
    inl-scan = trans (fl-go-skip pre (armG ++ X1) (ℓ o l) 0 (nolab-pre (ℓ o l)))
               (trans (fl-go-skip armG X1 (ℓ o l) 5 (noG (ℓ o l) l<l2))
                      (fl-hit (ℓ o l) (restore-input n ∷ load-indirect-suc ∷ (armF ++ post)) P₀))

    noF-e : NoLabel (ℓ o (suc l)) armF
    noF-e = noLabel-outside (ℓ o (suc l)) armF liArmF (λ w → 1+n≰n (proj₁ w))

    join-scan : find-label trace (ℓ o (suc l)) ≡ just J₀
    join-scan =
      trans (fl-go-skip pre (armG ++ X1) (ℓ o (suc l)) 0 (nolab-pre (ℓ o (suc l))))
     (trans (fl-go-skip armG X1 (ℓ o (suc l)) 5 (noG (ℓ o (suc l)) sl<l2))
     (trans (fl-go-skip midJ (armF ++ post) (ℓ o (suc l)) (5 + length armG) (nolab-mid (ℓ o (suc l)) ≤-refl))
     (trans (fl-go-skip armF post (ℓ o (suc l)) ((5 + length armG) + 4) noF-e)
            (fl-hit (ℓ o (suc l)) [] J₀))))

    ------------------------------------------------------------------
    -- AT A PLACEMENT.
    ------------------------------------------------------------------
    module At (prog : AbstractTrace) (b : ℕ) (span : SpanAt prog b trace) (lab : LabelsAt prog b trace) where

      P J : ℕ
      P = P₀ + b
      J = J₀ + b

      inl-target : find-label prog (ℓ o l) ≡ just P
      inl-target = lab (ℓ o l) P₀ inl-scan

      join-target : find-label prog (ℓ o (suc l)) ≡ just J
      join-target = lab (ℓ o (suc l)) J₀ join-scan

      spA : SpanAt prog (5 + b) (armG ++ X1)
      spA = span-drop prog pre {armG ++ X1} b span

      laA : LabelsAt prog (5 + b) (armG ++ X1)
      laA = labels-drop prog pre {armG ++ X1} b lab (λ m _ _ → nolab-pre m)

      spA′ : SpanAt prog (5 + b) (tG ++ (tail9 1 ++ X1))
      spA′ = subst (SpanAt prog (5 + b)) (++-assoc tG (tail9 1) X1) spA

      laA′ : LabelsAt prog (5 + b) (tG ++ (tail9 1 ++ X1))
      laA′ = subst (LabelsAt prog (5 + b)) (++-assoc tG (tail9 1) X1) laA

      -- the `inr` arm
      spG : SpanAt prog (5 + b) tG
      spG = span-take prog tG {tail9 1 ++ X1} (5 + b) spA′

      labG : LabelsAt prog (5 + b) tG
      labG = labels-take prog tG {tail9 1 ++ X1} (5 + b) laA′

      spGT : SpanAt prog (length tG + (5 + b)) (tail9 1 ++ X1)
      spGT = span-drop prog tG {tail9 1 ++ X1} (5 + b) spA′

      -- the `inl` arm
      spX1 : SpanAt prog (length armG + (5 + b)) X1
      spX1 = span-drop prog armG {X1} (5 + b) spA

      laX1 : LabelsAt prog (length armG + (5 + b)) X1
      laX1 = labels-drop prog armG {X1} (5 + b) laA
               (λ m j eq → noG m (proj₂ (found-in-window X1 m j eq liX1)))

      spLab : SpanAt prog P (instr-ctrl (c-label (ℓ o l)) ∷ restore-input n ∷ load-indirect-suc ∷ [])
      spLab = subst (λ z → SpanAt prog z (instr-ctrl (c-label (ℓ o l)) ∷ restore-input n ∷ load-indirect-suc ∷ [])) (sum-lab (length armG) b)
                (span-take prog (instr-ctrl (c-label (ℓ o l)) ∷ restore-input n ∷ load-indirect-suc ∷ []) {armF ++ post}
                  (1 + (length armG + (5 + b)))
                  (span-drop prog (instr-ctrl (c-jmp (ℓ o (suc l))) ∷ []) {instr-ctrl (c-label (ℓ o l)) ∷ restore-input n ∷ load-indirect-suc ∷ (armF ++ post)} (length armG + (5 + b)) spX1))

      spFP : SpanAt prog (4 + (length armG + (5 + b))) (armF ++ post)
      spFP = span-drop prog midJ {armF ++ post} (length armG + (5 + b)) spX1

      laFP : LabelsAt prog (4 + (length armG + (5 + b))) (armF ++ post)
      laFP = labels-drop prog midJ {armF ++ post} (length armG + (5 + b)) laX1
               (λ m j eq → nolab-mid m (proj₁ (found-in-window (armF ++ post) m j eq liFP)))

      spFP′ : SpanAt prog (3 + P) (tF ++ (tail9 0 ++ post))
      spFP′ = subst (SpanAt prog (3 + P)) (++-assoc tF (tail9 0) post)
                (subst (λ z → SpanAt prog z (armF ++ post)) (sum-shift-l (length armG) b) spFP)

      laFP′ : LabelsAt prog (3 + P) (tF ++ (tail9 0 ++ post))
      laFP′ = subst (LabelsAt prog (3 + P)) (++-assoc tF (tail9 0) post)
                (subst (λ z → LabelsAt prog z (armF ++ post)) (sum-shift-l (length armG) b) laFP)

      spF : SpanAt prog (3 + P) tF
      spF = span-take prog tF {tail9 0 ++ post} (3 + P) spFP′

      labF : LabelsAt prog (3 + P) tF
      labF = labels-take prog tF {tail9 0 ++ post} (3 + P) laFP′

      spFT : SpanAt prog (length tF + (3 + P)) (tail9 0 ++ post)
      spFT = span-drop prog tF {tail9 0 ++ post} (3 + P) spFP′

      -- the join label
      at-join : fetch prog J ≡ just (instr-ctrl (c-label (ℓ o (suc l))))
      at-join = subst (λ z → fetch prog z ≡ just (instr-ctrl (c-label (ℓ o (suc l))))) (sym (sum-join (length armG) (length armF) b))
                  (span-drop prog armF {post} (4 + (length armG + (5 + b))) spFP 0 _ refl)

      -- the two end pcs
      end-r : suc J ≡ length trace + b
      end-r = trans (sum-end-r (length armG) (length armF) b) (sym (cong (_+ b) len))

      end-l : suc (9 + (length tF + (3 + P))) ≡ length trace + b
      end-l = trans (sum-end-l (length armG) (length tF) b)
                    (sym (trans (cong (_+ b) len)
                                (cong (λ z → (5 + (length armG + (4 + (z + 1)))) + b) lenF)))
