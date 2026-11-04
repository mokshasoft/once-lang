-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.SumShape
--
-- plan 0.135 S3 / plan 0.123 α2: the re-suspension at a SUM layer — its
-- text, where every row sits, and the two jump targets. Slots src = n,
-- dst = n+1, tmp = n+2; labels l (inl) and l+1 (join):
--
--   store-at-slot src ; restore-input src ; c-branch-tag-zero l
--   ARM 1 G tG                                     -- inr: falls through
--   c-jmp (l+1) ; c-label l
--   ARM 0 F tF                                     -- inl
--   c-label (l+1)
--
--   ARM tag P t = restore-input src ; get (P A) 1 ; t ;
--                 store-at-slot tmp ; alloc (2 ⊔ sz) ; store-at-slot dst ;
--                 mov-to-input ; load-tag-lit tag ; store-at 0 ;
--                 fill (1 + |Pν|) (sz ∸ (1 + |Pν|)) ; put Pν tmp dst 1 ; load-from-slot dst
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
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; LabelIn; li-none; li-lab)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-branch-tag-zero; c-jmp; c-label; store-at-slot; restore-input;
         instr-alloc-heap; mov-to-input; instr-load-tag-lit; store-at; load-from-slot)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ; LabelId; module LabelId)
open LabelId using (idx)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; wf-Sum; ⟦_⟧TI; ν-type) renaming (_+_ to _+ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (get; get-All; put; put-All; fill; fill-All)
open import Relation.Nullary using (¬_)
open import Data.Nat using (_⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (1+n≰n)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

module ResuspSumShapeC {FS : FrameSemantics} where

  open Core {FS}
  open ResuspBaseC {FS}
  open FlatStepsAPI {FS} using (fl-go-skip)
  open Resolve {FS} using (NoLabel; found-in-window; noLabel-outside; fl-hit)

  just-injL : ∀ {a b : LabelId} → just a ≡ just b → a ≡ b
  just-injL refl = refl

  -- no labels in a read, a fill or a put
  nolab-get : ∀ (X′ : IRTy) k m → NoLabel m (get X′ k)
  nolab-get X′ k m = get-All {λ i → ¬ (label-of? i ≡ just m)} X′ k (λ _ ()) (λ _ ()) (λ ())

  li-get : ∀ {lo hi} (X′ : IRTy) k → LabelsIn lo hi (get X′ k)
  li-get X′ k = get-All {LabelIn _ _} X′ k (λ _ → li-none refl) (λ _ → li-none refl) (li-none refl)

  li-put : ∀ {lo hi} (X′ : IRTy) st bl off → LabelsIn lo hi (put X′ st bl off)
  li-put X′ st bl off = put-All {LabelIn _ _} X′ st bl off (li-none refl) (li-none refl) (li-none refl)
                          (λ _ → li-none refl) (λ _ → li-none refl)

  li-fill : ∀ {lo hi} from c → LabelsIn lo hi (fill from c)
  li-fill from c = fill-All {LabelIn _ _} from c (li-none refl) (λ _ → li-none refl)

  module SumShape (F : IRFunctor) (E A : IRTy) (lbl-n : ℕ) {G₁ G₂ : IRFunctor}
                  (wF : WellFormedFI G₁) (wG : WellFormedFI G₂) (n l : ℕ) where

    lbl : LabelId
    lbl = ℓ o lbl-n

    X : IRTy
    X = ν-type F

    dst tmp nF : ℕ
    dst = suc n
    tmp = suc dst
    nF  = suc tmp

    Fν Gν : IRTy
    Fν = ⟦ G₁ ⟧TI X
    Gν = ⟦ G₂ ⟧TI X

    sz : ℕ
    sz = size (Fν +ᵀ Gν)

    n2 l2 l3 : ℕ
    n2 = proj₁ (resuspend-layer F E A nF (suc (suc l)) lbl 0 wF)
    l2 = proj₁ (proj₂ (resuspend-layer F E A nF (suc (suc l)) lbl 0 wF))
    l3 = proj₁ (proj₂ (resuspend-layer F E A n2 l2 lbl 0 wG))

    -- an arm's build, after its payload's re-suspension
    ST : ℕ → IRTy → AbstractTrace
    ST tag Pν = store-at-slot tmp ∷ instr-alloc-heap (2 ⊔ sz) ∷ store-at-slot dst ∷ mov-to-input ∷
                instr-load-tag-lit tag ∷ store-at 0 ∷
                (fill (suc (size Pν)) (sz ∸ suc (size Pν)) DL.++ put Pν tmp dst 1 DL.++ load-from-slot dst ∷ [])

    ARM : ℕ → IRTy → IRTy → AbstractTrace → AbstractTrace
    ARM tag Pa Pν t = restore-input n ∷ (get Pa 1 DL.++ t DL.++ ST tag Pν)

    tF tG pre armG midJ armF post : AbstractTrace
    tF   = proj₂ (proj₂ (resuspend-layer F E A nF (suc (suc l)) lbl 0 wF))
    tG   = proj₂ (proj₂ (resuspend-layer F E A n2 l2 lbl 0 wG))
    pre  = store-at-slot n ∷ restore-input n ∷ instr-ctrl (c-branch-tag-zero (ℓ o l)) ∷ []
    armG = ARM 1 (⟦ G₂ ⟧TI A) Gν tG
    midJ = instr-ctrl (c-jmp (ℓ o (suc l))) ∷ instr-ctrl (c-label (ℓ o l)) ∷ []
    armF = ARM 0 (⟦ G₁ ⟧TI A) Fν tF
    post = instr-ctrl (c-label (ℓ o (suc l))) ∷ []

    trace : AbstractTrace
    trace = proj₂ (proj₂ (resuspend-layer F E A n l lbl 0 (wf-Sum wF wG)))

    shape : trace ≡ pre DL.++ (armG DL.++ (midJ DL.++ (armF DL.++ post)))
    shape = refl

    len : length trace ≡ 3 + (length armG + (2 + (length armF + 1)))
    len = cong (3 +_) (trans (length-++ armG {midJ DL.++ (armF DL.++ post)})
                             (cong (λ z → length armG + (2 + z)) (length-++ armF {post})))

    ------------------------------------------------------------------
    -- LABEL WINDOWS.
    ------------------------------------------------------------------
    ssl≤l2 : suc (suc l) ≤ l2
    ssl≤l2 = resuspend-label-mono F E A nF (suc (suc l)) lbl 0 wF

    sl<l2 : suc l < l2
    sl<l2 = ssl≤l2
    l<l2 : l < l2
    l<l2 = ≤-trans (n≤1+n (suc l)) ssl≤l2

    li-ST : ∀ {lo hi} tag (Pν : IRTy) → LabelsIn lo hi (ST tag Pν)
    li-ST tag Pν = li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷ li-none refl ∷
                   ++⁺ (li-fill (suc (size Pν)) (sz ∸ suc (size Pν))) (++⁺ (li-put Pν tmp dst 1) (li-none refl ∷ []))

    li-ARM : ∀ {lo hi} tag (Pa Pν : IRTy) (t : AbstractTrace) → LabelsIn lo hi t → LabelsIn lo hi (ARM tag Pa Pν t)
    li-ARM tag Pa Pν t lt = li-none refl ∷ ++⁺ (li-get Pa 1) (++⁺ lt (li-ST tag Pν))

    liArmG : LabelsIn l2 l3 armG
    liArmG = li-ARM 1 (⟦ G₂ ⟧TI A) Gν tG (resuspend-labels-in l2 l3 F E A n2 l2 lbl 0 wG ≤-refl ≤-refl)

    liArmF : LabelsIn (suc (suc l)) l2 armF
    liArmF = li-ARM 0 (⟦ G₁ ⟧TI A) Fν tF (resuspend-labels-in (suc (suc l)) l2 F E A nF (suc (suc l)) lbl 0 wF ≤-refl ≤-refl)

    -- armF ++ post resolves in [suc l, l2)
    liFP : LabelsIn (suc l) l2 (armF DL.++ post)
    liFP = ++⁺ (li-ARM 0 (⟦ G₁ ⟧TI A) Fν tF (resuspend-labels-in (suc l) l2 F E A nF (suc (suc l)) lbl 0 wF (n≤1+n (suc l)) ≤-refl))
               (li-lab refl ≤-refl sl<l2 ∷ [])

    -- the rest after armG resolves in [l, l2)
    liX1 : LabelsIn l l2 (midJ DL.++ (armF DL.++ post))
    liX1 = li-lab refl (n≤1+n l) sl<l2 ∷ li-lab refl ≤-refl l<l2 ∷
           ++⁺ (li-ARM 0 (⟦ G₁ ⟧TI A) Fν tF (resuspend-labels-in l l2 F E A nF (suc (suc l)) lbl 0 wF (≤-trans (n≤1+n l) (n≤1+n (suc l))) ≤-refl))
               (li-lab refl (n≤1+n l) sl<l2 ∷ [])

    nolab-pre : ∀ m → NoLabel m pre
    nolab-pre m = (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []

    -- the mid rows define `ℓ l` only
    nolab-mid : ∀ m → suc l ≤ idx m → NoLabel m midJ
    nolab-mid m h = (λ ()) ∷ (λ eq → 1+n≰n (subst (suc l ≤_) (sym (cong idx (just-injL eq))) h)) ∷ []

    noG : ∀ m → idx m < l2 → NoLabel m armG
    noG m h = noLabel-outside m armG liArmG (λ w → 1+n≰n (≤-trans h (proj₁ w)))

    ------------------------------------------------------------------
    -- THE TWO JUMP TARGETS.
    ------------------------------------------------------------------
    P₀ J₀ : ℕ
    P₀ = suc (3 + length armG)
    J₀ = ((3 + length armG) + 2) + length armF

    inl-scan : find-label trace (ℓ o l) ≡ just P₀
    inl-scan = trans (fl-go-skip pre (armG DL.++ (midJ DL.++ (armF DL.++ post))) (ℓ o l) 0 (nolab-pre (ℓ o l)))
               (trans (fl-go-skip armG (midJ DL.++ (armF DL.++ post)) (ℓ o l) 3 (noG (ℓ o l) l<l2))
                      (fl-hit (ℓ o l) (armF DL.++ post) P₀))

    noF-e : NoLabel (ℓ o (suc l)) armF
    noF-e = noLabel-outside (ℓ o (suc l)) armF liArmF (λ w → 1+n≰n (proj₁ w))

    join-scan : find-label trace (ℓ o (suc l)) ≡ just J₀
    join-scan =
      trans (fl-go-skip pre (armG DL.++ (midJ DL.++ (armF DL.++ post))) (ℓ o (suc l)) 0 (nolab-pre (ℓ o (suc l))))
     (trans (fl-go-skip armG (midJ DL.++ (armF DL.++ post)) (ℓ o (suc l)) 3 (noG (ℓ o (suc l)) sl<l2))
     (trans (fl-go-skip midJ (armF DL.++ post) (ℓ o (suc l)) (3 + length armG) (nolab-mid (ℓ o (suc l)) ≤-refl))
     (trans (fl-go-skip armF post (ℓ o (suc l)) ((3 + length armG) + 2) noF-e)
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

      at-pre : SpanAt prog b pre
      at-pre = span-take prog pre {armG DL.++ (midJ DL.++ (armF DL.++ post))} b span

      spA : SpanAt prog (3 + b) (armG DL.++ (midJ DL.++ (armF DL.++ post)))
      spA = span-drop prog pre {armG DL.++ (midJ DL.++ (armF DL.++ post))} b span

      laA : LabelsAt prog (3 + b) (armG DL.++ (midJ DL.++ (armF DL.++ post)))
      laA = labels-drop prog pre {armG DL.++ (midJ DL.++ (armF DL.++ post))} b lab (λ m _ _ → nolab-pre m)

      -- the `inr` arm
      spG : SpanAt prog (3 + b) armG
      spG = span-take prog armG {midJ DL.++ (armF DL.++ post)} (3 + b) spA

      labG : LabelsAt prog (3 + b) armG
      labG = labels-take prog armG {midJ DL.++ (armF DL.++ post)} (3 + b) laA

      spX1 : SpanAt prog (length armG + (3 + b)) (midJ DL.++ (armF DL.++ post))
      spX1 = span-drop prog armG {midJ DL.++ (armF DL.++ post)} (3 + b) spA

      laX1 : LabelsAt prog (length armG + (3 + b)) (midJ DL.++ (armF DL.++ post))
      laX1 = labels-drop prog armG {midJ DL.++ (armF DL.++ post)} (3 + b) laA
               (λ m j eq → noG m (proj₂ (found-in-window (midJ DL.++ (armF DL.++ post)) m j eq liX1)))

      at-jmp : fetch prog (length armG + (3 + b)) ≡ just (instr-ctrl (c-jmp (ℓ o (suc l))))
      at-jmp = spX1 0 _ refl

      at-lab : fetch prog P ≡ just (instr-ctrl (c-label (ℓ o l)))
      at-lab = subst (λ z → fetch prog z ≡ just (instr-ctrl (c-label (ℓ o l)))) (arith (length armG) b) (spX1 1 _ refl)
        where arith : ∀ a b → 1 + (a + (3 + b)) ≡ suc (3 + a) + b
              arith = solve 2 (λ a b → con 1 :+ (a :+ (con 3 :+ b)) := (con 1 :+ (con 3 :+ a)) :+ b) refl

      -- the `inl` arm
      spFP : SpanAt prog (suc P) (armF DL.++ post)
      spFP = subst (λ z → SpanAt prog z (armF DL.++ post)) (arith (length armG) b)
               (span-drop prog midJ {armF DL.++ post} (length armG + (3 + b)) spX1)
        where arith : ∀ a b → 2 + (a + (3 + b)) ≡ suc (suc (3 + a) + b)
              arith = solve 2 (λ a b → con 2 :+ (a :+ (con 3 :+ b)) := con 1 :+ ((con 1 :+ (con 3 :+ a)) :+ b)) refl

      laFP : LabelsAt prog (suc P) (armF DL.++ post)
      laFP = subst (λ z → LabelsAt prog z (armF DL.++ post)) (arith (length armG) b)
               (labels-drop prog midJ {armF DL.++ post} (length armG + (3 + b)) laX1
                  (λ m j eq → nolab-mid m (proj₁ (found-in-window (armF DL.++ post) m j eq liFP))))
        where arith : ∀ a b → 2 + (a + (3 + b)) ≡ suc (suc (3 + a) + b)
              arith = solve 2 (λ a b → con 2 :+ (a :+ (con 3 :+ b)) := con 1 :+ ((con 1 :+ (con 3 :+ a)) :+ b)) refl

      spF : SpanAt prog (suc P) armF
      spF = span-take prog armF {post} (suc P) spFP

      labF : LabelsAt prog (suc P) armF
      labF = labels-take prog armF {post} (suc P) laFP

      -- the join label, after either arm
      at-join-l : fetch prog (length armF + suc P) ≡ just (instr-ctrl (c-label (ℓ o (suc l))))
      at-join-l = span-drop prog armF {post} (suc P) spFP 0 _ refl

      at-join : fetch prog J ≡ just (instr-ctrl (c-label (ℓ o (suc l))))
      at-join = subst (λ z → fetch prog z ≡ just (instr-ctrl (c-label (ℓ o (suc l))))) (join-eq (length armG) (length armF) b) at-join-l
        where join-eq : ∀ a f b → f + suc (suc (3 + a) + b) ≡ (((3 + a) + 2) + f) + b
              join-eq = solve 3 (λ a f b → f :+ (con 1 :+ ((con 1 :+ (con 3 :+ a)) :+ b))
                                         := (((con 3 :+ a) :+ con 2) :+ f) :+ b) refl

      -- …and the end pc
      end : suc J ≡ length trace + b
      end = trans (arith (length armG) (length armF) b) (sym (cong (_+ b) len))
        where arith : ∀ a f b → suc ((((3 + a) + 2) + f) + b) ≡ (3 + (a + (2 + (f + 1)))) + b
              arith = solve 3 (λ a f b → con 1 :+ ((((con 3 :+ a) :+ con 2) :+ f) :+ b)
                                       := (con 3 :+ (a :+ (con 2 :+ (f :+ con 1)))) :+ b) refl

      -- the inl path joins where the inr path's jump lands
      join-l : length armF + suc P ≡ J
      join-l = arith (length armG) (length armF) b
        where arith : ∀ a f b → f + suc (suc (3 + a) + b) ≡ (((3 + a) + 2) + f) + b
              arith = solve 3 (λ a f b → f :+ (con 1 :+ ((con 1 :+ (con 3 :+ a)) :+ b))
                                       := (((con 3 :+ a) :+ con 2) :+ f) :+ b) refl
