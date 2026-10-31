-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FoldText   (plan 0.125 S3, cata M4 stage D1b)
--
-- WHERE THE PARTS OF THE FOLD LOOP SIT, past the flatten loop (`Text.At`'s
-- `span-rest`: the text `R` at the fold head `X = length flatTxt + H`):
--
--     X+0 … X+7     ℓ (l1+2): load eval · mov-to-input · branch-tag-zero ℓ (l1+3) ·
--                   load-indirect-suc · store eval · load-indirect · mov-to-input   (`hd8`)
--     X+8 …         rebuild-walk (n+2) (n+4) (n+5) G (n+7) (l1+4+lsize G)          (`rbTxt`, RL rows)
--     RL+8+X        mov-to-input
--     Y = 1+RL+8+X  the call's fourteen rows, `instr-call-closure` at 14+Y
--     15+Y …        push2 val (ten rows), `c-jmp ℓ (l1+2)` at 25+Y,
--                   `ℓ (l1+3)` at 26+Y, then load val · mov-to-input · load-indirect
--     30+Y          `c-jmp ℓ (bodyL+1)`, the body's marker at 31+Y, the algebra
--                   from 32+Y, its `c-ret`, and the end label at (33+|at|)+Y.
--
-- The label scans (`head-label`, `exit-label`, `end-label`, the rebuild
-- walk's and the algebra's own windows) are each one `NoLabel` over the text
-- before the label, assembled from the pieces' label windows (`LabelScope`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.FoldText (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module CataBrTextC; init-rows)
open import Once.CCC.Codegen.IRToTrace o
  using (cata-call-setup; cata-call; cata-body; cata-br-I₂; push2; visit-walk; rebuild-walk; fsize; lsize)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (visit-ls; rebuild-ls; push2-ls; cata-setup-ls; cata-call-ls; labels-in)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; li-none; li-lab)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-jmp; c-label; c-branch-tag-zero; c-thunk; c-ret; load-from-slot; store-at-slot
        ; mov-to-input; mov-to-output; load-indirect; load-indirect-suc; instr-call-closure; block-layout)
open import Once.CCC.Label using (ℓ; LabelId; module LabelId)
open LabelId using (idx)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F)
import Once.IRTy as IRTy′
open import Once.Internal.Type using (Functor)
open import Data.Nat using (s≤s; z≤n)
open import Data.Nat.Properties using (+-monoʳ-<; +-monoʳ-≤)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Relation.Unary.All using (All) renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

private
  -- the pcs, as arithmetic
  pos-cut : ∀ (f r w b : ℕ) → (37 + (f + (8 + (r + suc w)))) + b ≡ w + suc (r + (8 + (f + (37 + b))))
  pos-cut = solve 4 (λ f r w b → (con 37 :+ (f :+ (con 8 :+ (r :+ (con 1 :+ w))))) :+ b
                                 := w :+ (con 1 :+ (r :+ (con 8 :+ (f :+ (con 37 :+ b)))))) refl

  pos-rb : ∀ (j f b : ℕ) → (j + (37 + (f + 8))) + b ≡ j + (8 + (f + (37 + b)))
  pos-rb = solve 3 (λ j f b → (j :+ (con 37 :+ (f :+ con 8))) :+ b := j :+ (con 8 :+ (f :+ (con 37 :+ b)))) refl

  pos-hd : ∀ (f b : ℕ) → (37 + f) + b ≡ f + (37 + b)
  pos-hd = solve 2 (λ f b → (con 37 :+ f) :+ b := f :+ (con 37 :+ b)) refl

  len-t : ∀ (a : ℕ) → 32 + (a + 2) ≡ 34 + a
  len-t = solve 1 (λ a → con 32 :+ (a :+ con 2) := con 34 :+ a) refl

  len-e : ∀ (a : ℕ) → 32 + (a + 1) ≡ 33 + a
  len-e = solve 1 (λ a → con 32 :+ (a :+ con 1) := con 33 :+ a) refl

-- the fold loop's head (`Pieces.foldTxt`'s first eight rows), for slot base `n`, label base `l1`
fold-hd : ℕ → ℕ → AbstractTrace
fold-hd n l1 =
  instr-ctrl (c-label (ℓ o (l1 + 2))) ∷
  load-from-slot (suc n) ∷ mov-to-input ∷
  instr-ctrl (c-branch-tag-zero (ℓ o (l1 + 3))) ∷
  load-indirect-suc ∷ store-at-slot (suc n) ∷
  load-indirect ∷ mov-to-input ∷ []

module CataFoldTextC {FS : FrameSemantics} where

  open Core {FS}
  open ResuspBaseC {FS} using (span-take; span-drop)
  open Resolve {FS} using (NoLabel; noLabel-outside; label-resolves; found-in-window)
  open FlatStepsAPI {FS} using (find-label-distrib)
  open CataBrTextC {FS} using (module Text)

  -- a piece whose label window misses `m` defines no `m`
  nl-out : ∀ {lo hi} (t : AbstractTrace) → LabelsIn lo hi t → ∀ (m : LabelId) → (idx m < lo) ⊎ (hi ≤ idx m) → NoLabel m t
  nl-out t li m (inj₁ p) = noLabel-outside m t li (λ w → <-irrefl refl (<-≤-trans p (proj₁ w)))
  nl-out t li m (inj₂ p) = noLabel-outside m t li (λ w → <-irrefl refl (<-≤-trans (proj₂ w) p))

  private
    idx-of : Maybe LabelId → ℕ
    idx-of (just m) = idx m
    idx-of nothing  = 0

  -- one label row, for a label other than its own
  nl-row : ∀ {a : ℕ} (m : LabelId) → a ≢ idx m → ¬ (label-of? (instr-ctrl (c-label (ℓ o a))) ≡ just m)
  nl-row m ne e = ne (cong idx-of e)

  module FoldAt {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C) (n l : ℕ)
                (prog : AbstractTrace) (base : ℕ)
                (span : SpanAt prog base (Text.text′ wf alg n l))
                (la : LabelsAt prog base (Text.text′ wf alg n l)) where

    module T = Text wf alg n l
    open T using (G; l1; bb; at; tailTxt; R; text′)
    open T.Pc using (cslot; bodyL; pre37; flatTxt; headTxt; pushTxt; reloadTxt; visitTxt; exitTxt; foldTxt
                    ; setupTxt; initTxt; rootTxt)
    module TA = T.At prog base span la

    ------------------------------------------------------------------
    -- THE PIECES of `R`.
    ------------------------------------------------------------------
    headL exitL endL : LabelId
    headL = ℓ o (l1 + 2)
    exitL = ℓ o (l1 + 3)
    endL  = ℓ o (bodyL + 1)

    lr : ℕ
    lr = l1 + 4 + lsize G

    hd8 rbTxt callTxt pushV post2 : AbstractTrace
    hd8 = fold-hd n l1
    rbTxt = rebuild-walk (n + 2) (n + 4) (n + 5) G (n + 7) lr
    callTxt = cata-call cslot (cslot + 1) (cslot + 2) (cslot + 3)
    pushV = push2 (n + 2) (n + 4) (n + 5)
    post2 = instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label endL) ∷ []

    -- the first 32 rows of `tailTxt` (up to and including the body's marker)
    pre32 : AbstractTrace
    pre32 = callTxt ++ (pushV ++ (instr-ctrl (c-jmp headL) ∷ instr-ctrl (c-label exitL) ∷
              load-from-slot (n + 2) ∷ mov-to-input ∷ load-indirect ∷
              instr-ctrl (c-jmp endL) ∷ instr-ctrl (c-thunk (ℓ o bodyL) bb) ∷ []))

    -- …and up to the exit label
    pre26 : AbstractTrace
    pre26 = callTxt ++ (pushV ++ (instr-ctrl (c-jmp headL) ∷ []))

    RL : ℕ
    RL = length rbTxt

    tail-eq : tailTxt ≡ pre32 ++ (at ++ post2)
    tail-eq = refl

    R-eq : R ≡ hd8 ++ (rbTxt ++ (mov-to-input ∷ tailTxt))
    R-eq = cong (hd8 ++_) (++-assoc rbTxt (mov-to-input ∷ []) tailTxt)

    -- the text before row `W` of the tail
    PRE : AbstractTrace → AbstractTrace
    PRE W = pre37 ++ (flatTxt ++ (hd8 ++ (rbTxt ++ (mov-to-input ∷ W))))

    cut : ∀ (W Z : AbstractTrace) → tailTxt ≡ W ++ Z → text′ ≡ PRE W ++ Z
    cut W Z e =
      trans (cong (λ t → pre37 ++ (flatTxt ++ t)) (trans R-eq (cong (λ t → hd8 ++ (rbTxt ++ (mov-to-input ∷ t))) e)))
      (cong (pre37 ++_)
        (trans (cong (λ t → flatTxt ++ (hd8 ++ t)) (sym (++-assoc rbTxt (mov-to-input ∷ W) Z)))
               (sym (++-assoc flatTxt (hd8 ++ (rbTxt ++ (mov-to-input ∷ W))) Z))))

    len-PRE : ∀ (W : AbstractTrace) → length (PRE W) ≡ 37 + (length flatTxt + (8 + (RL + suc (length W))))
    len-PRE W =
      cong (37 +_) (trans (length-++ flatTxt {hd8 ++ (rbTxt ++ (mov-to-input ∷ W))})
                          (cong (λ z → length flatTxt + (8 + z)) (length-++ rbTxt {mov-to-input ∷ W})))

    ------------------------------------------------------------------
    -- THE PCS.
    ------------------------------------------------------------------
    X Y : ℕ
    X = length flatTxt + TA.H
    Y = suc (RL + (8 + X))

    -- the text before row `W` of the tail ends at `length W + Y`
    pre-pc : ∀ (W : AbstractTrace) → length (PRE W) + base ≡ length W + Y
    pre-pc W = trans e1 (pos-cut (length flatTxt) RL (length W) base)
      where
        e1 : length (PRE W) + base ≡ (37 + (length flatTxt + (8 + (RL + suc (length W))))) + base
        e1 = cong (_+ base) {length (PRE W)} {37 + (length flatTxt + (8 + (RL + suc (length W))))} (len-PRE W)

    ------------------------------------------------------------------
    -- SPANS AND ROWS.
    ------------------------------------------------------------------
    span-R : SpanAt prog X (hd8 ++ (rbTxt ++ (mov-to-input ∷ tailTxt)))
    span-R = subst (SpanAt prog X) R-eq TA.span-rest

    span-hd : SpanAt prog X hd8
    span-hd = span-take prog hd8 X span-R

    private
      sp1 : SpanAt prog (8 + X) (rbTxt ++ (mov-to-input ∷ tailTxt))
      sp1 = span-drop prog hd8 X span-R
      sp2 : SpanAt prog (RL + (8 + X)) (mov-to-input ∷ tailTxt)
      sp2 = span-drop prog rbTxt (8 + X) sp1

    span-rb : SpanAt prog (8 + X) rbTxt
    span-rb = span-take prog rbTxt (8 + X) sp1

    fetch-mti : fetch prog (RL + (8 + X)) ≡ just mov-to-input
    fetch-mti = sp2 0 _ refl

    span-tail : SpanAt prog Y tailTxt
    span-tail = span-drop prog (mov-to-input ∷ []) (RL + (8 + X)) sp2

    span-call : SpanAt prog Y callTxt
    span-call = span-take prog callTxt Y span-tail

    fetch-cc : fetch prog (14 + Y) ≡ just instr-call-closure
    fetch-cc = span-tail 14 _ refl

    span-push : SpanAt prog (15 + Y) pushV
    span-push = span-take prog pushV (15 + Y) (span-drop prog callTxt Y span-tail)

    fetch-jmp-head : fetch prog (25 + Y) ≡ just (instr-ctrl (c-jmp headL))
    fetch-jmp-head = span-tail 25 _ refl

    fetch-exit : fetch prog (26 + Y) ≡ just (instr-ctrl (c-label exitL))
    fetch-exit = span-tail 26 _ refl

    fetch-ld : fetch prog (27 + Y) ≡ just (load-from-slot (n + 2))
    fetch-ld = span-tail 27 _ refl

    fetch-mti2 : fetch prog (28 + Y) ≡ just mov-to-input
    fetch-mti2 = span-tail 28 _ refl

    fetch-li : fetch prog (29 + Y) ≡ just load-indirect
    fetch-li = span-tail 29 _ refl

    fetch-jmp-end : fetch prog (30 + Y) ≡ just (instr-ctrl (c-jmp endL))
    fetch-jmp-end = span-tail 30 _ refl

    fetch-thunk : fetch prog (31 + Y) ≡ just (instr-ctrl (c-thunk (ℓ o bodyL) bb))
    fetch-thunk = span-tail 31 _ refl

    fetch-end : fetch prog ((33 + length at) + Y) ≡ just (instr-ctrl (c-label endL))
    fetch-end = span-tail (33 + length at) _
                  (trans (fetch-++-right pre32 (at ++ post2) (suc (length at)))
                         (subst (λ z → fetch (at ++ post2) z ≡ just (instr-ctrl (c-label endL)))
                                (+-comm (length at) 1) (fetch-++-right at post2 1)))

    body-span : SpanAt prog (31 + Y) (block-layout (ℓ o bodyL , bb , at))
    body-span = span-take prog (block-layout (ℓ o bodyL , bb , at)) {instr-ctrl (c-label endL) ∷ []} (31 + Y)
                  (subst (λ t → SpanAt prog (31 + Y) (instr-ctrl (c-thunk (ℓ o bodyL) bb) ∷ t))
                         (sym (++-assoc at (instr-ctrl (c-ret bb) ∷ []) (instr-ctrl (c-label endL) ∷ [])))
                         (span-drop prog (callTxt ++ (pushV ++ (instr-ctrl (c-jmp headL) ∷ instr-ctrl (c-label exitL) ∷
                                            load-from-slot (n + 2) ∷ mov-to-input ∷ load-indirect ∷
                                            instr-ctrl (c-jmp endL) ∷ [])))
                                    Y span-tail))

    -- where the cata ends
    text-PRE : text′ ≡ PRE tailTxt
    text-PRE = cong (λ t → pre37 ++ (flatTxt ++ t)) R-eq

    len-end : length text′ + base ≡ (34 + length at) + Y
    len-end = trans e1 (trans (pre-pc tailTxt) (cong (_+ Y) {length tailTxt} {34 + length at} e2))
      where
        e1 : length text′ + base ≡ length (PRE tailTxt) + base
        e1 = cong (λ t → length t + base) {text′} {PRE tailTxt} text-PRE
        e2 : length tailTxt ≡ 34 + length at
        e2 = trans (cong (32 +_) {length (at ++ post2)} {length at + 2} (length-++ at {post2})) (len-t (length at))

    ------------------------------------------------------------------
    -- THE LABEL WINDOWS of the pieces before the fold's labels.
    ------------------------------------------------------------------
    private
      lt : ∀ (a k : ℕ) → a < a + suc k
      lt a k = subst (a <_) (sym (+-suc a k)) (s≤s (m≤m+n a k))

      lt-ne : ∀ {a b : ℕ} → a < b → a ≢ b
      lt-ne p e = <-irrefl e p

      s1<2 : suc l1 < l1 + 2
      s1<2 = subst (_< l1 + 2) (+-comm l1 1) (+-monoʳ-< l1 (s≤s (s≤s z≤n)))

      L-pre37 : LabelsIn 0 0 pre37
      L-pre37 =
        ++⁺ (cata-setup-ls 0 0 _ _ _ _)
        (++⁺ (li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
              li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ []ᴬ)
             (push2-ls 0 0 n (n + 4) (n + 5)))

      L-head : LabelsIn l1 (l1 + 2) headTxt
      L-head = li-lab refl ≤-refl (lt l1 1) ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-lab refl (n≤1+n l1) s1<2 ∷ᴬ
               li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ []ᴬ

      L-exit : LabelsIn l1 (l1 + 2) exitTxt
      L-exit = li-lab refl ≤-refl (lt l1 1) ∷ᴬ li-lab refl (n≤1+n l1) s1<2 ∷ᴬ []ᴬ

      L-visit : LabelsIn (l1 + 4) (l1 + 4 + lsize G) visitTxt
      L-visit = visit-ls G n (n + 4) (n + 5) (n + 7) (l1 + 4)

      L-hd8 : LabelsIn (l1 + 2) (l1 + 4) hd8
      L-hd8 = li-lab refl ≤-refl (+-monoʳ-< l1 (s≤s (s≤s (s≤s z≤n)))) ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
              li-lab refl (+-monoʳ-≤ l1 (s≤s (s≤s z≤n))) (+-monoʳ-< l1 (s≤s (s≤s (s≤s (s≤s z≤n))))) ∷ᴬ
              li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ []ᴬ

      L-rb : LabelsIn lr (lr + lsize G) rbTxt
      L-rb = rebuild-ls G (n + 2) (n + 4) (n + 5) (n + 7) lr

      L-at : LabelsIn l l1 at
      L-at = labels-in alg 0 l

      nl-nolab : ∀ (m : LabelId) (t : AbstractTrace) → LabelsIn 0 0 t → NoLabel m t
      nl-nolab m t li = nl-out t li m (inj₂ z≤n)

      nl-pre37 : ∀ (m : LabelId) → NoLabel m pre37
      nl-pre37 m = nl-nolab m pre37 L-pre37

      -- the flatten loop, piece by piece
      nl-flat : ∀ (m : LabelId) → (idx m < l1) ⊎ (l1 + 2 ≤ idx m)
              → (idx m < l1 + 4) ⊎ (l1 + 4 + lsize G ≤ idx m) → NoLabel m flatTxt
      nl-flat m p q =
        ++⁺ (nl-out headTxt L-head m p)
        (++⁺ (nl-nolab m pushTxt (push2-ls 0 0 (suc n) (n + 4) (n + 5)))
        (++⁺ (nl-nolab m reloadTxt (li-none refl ∷ᴬ li-none refl ∷ᴬ []ᴬ))
        (++⁺ (nl-out visitTxt L-visit m q) (nl-out exitTxt L-exit m p))))

      nl-call : ∀ (m : LabelId) → NoLabel m callTxt
      nl-call m = nl-nolab m callTxt (cata-call-ls 0 0 _ _ _ _)

      nl-push : ∀ (m : LabelId) → NoLabel m pushV
      nl-push m = nl-nolab m pushV (push2-ls 0 0 (n + 2) (n + 4) (n + 5))

      -- the first 32 rows of the tail, for a label that is not `ℓ (l1+3)`
      nl-pre32 : ∀ (m : LabelId) → l1 + 3 ≢ idx m → NoLabel m pre32
      nl-pre32 m ne =
        ++⁺ (nl-call m) (++⁺ (nl-push m)
          ((λ ()) ∷ᴬ nl-row m ne ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ))

      nl-PRE : ∀ (m : LabelId) (W : AbstractTrace) → NoLabel m flatTxt → NoLabel m hd8 → NoLabel m rbTxt → NoLabel m W
             → NoLabel m (PRE W)
      nl-PRE m W a b c d = ++⁺ (nl-pre37 m) (++⁺ a (++⁺ b (++⁺ c ((λ ()) ∷ᴬ d))))

      up4 : l1 + 4 ≤ bodyL
      up4 = ≤-trans (m≤m+n (l1 + 4) (lsize G)) (m≤m+n lr (lsize G))

      bl1 : bodyL ≤ bodyL + 1
      bl1 = m≤m+n bodyL 1

      l3<4 : l1 + 3 < l1 + 4
      l3<4 = +-monoʳ-< l1 (s≤s (s≤s (s≤s (s≤s z≤n))))

      l2≤3 : l1 + 2 ≤ l1 + 3
      l2≤3 = +-monoʳ-≤ l1 (s≤s (s≤s z≤n))

      l2≤4 : l1 + 2 ≤ l1 + 4
      l2≤4 = +-monoʳ-≤ l1 (s≤s (s≤s z≤n))

      l≤2 : l1 ≤ l1 + 2
      l≤2 = m≤m+n l1 2

      -- a label resolved at a row of the tail
      resolve : ∀ (W Z : AbstractTrace) (m : LabelId) → tailTxt ≡ W ++ (instr-ctrl (c-label m) ∷ Z) → NoLabel m (PRE W)
              → find-label prog m ≡ just (length W + Y)
      resolve W Z m e nl =
        trans (la m _ (trans (cong (λ t → find-label t m) (cut W (instr-ctrl (c-label m) ∷ Z) e))
                             (label-resolves (PRE W) m Z nl)))
              (cong just (trans (cong (_+ base) {length (PRE W) + 0} {length (PRE W)} (+-identityʳ (length (PRE W)))) (pre-pc W)))

    ------------------------------------------------------------------
    -- THE LABELS.
    ------------------------------------------------------------------
    -- the fold head
    head-label : find-label prog headL ≡ just X
    head-label = trans (la headL (37 + length flatTxt) scan) (cong just (pos-hd (length flatTxt) base))
      where
        nl : NoLabel headL (pre37 ++ flatTxt)
        nl = ++⁺ (nl-pre37 headL) (nl-flat headL (inj₂ ≤-refl) (inj₁ (+-monoʳ-< l1 (s≤s (s≤s (s≤s z≤n))))))
        scan : find-label text′ headL ≡ just (37 + length flatTxt)
        post : AbstractTrace
        post = (load-from-slot (suc n) ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero exitL) ∷
                load-indirect-suc ∷ store-at-slot (suc n) ∷ load-indirect ∷ mov-to-input ∷ []) ++ ((rbTxt ++ (mov-to-input ∷ [])) ++ tailTxt)
        scan = trans (cong (λ t → find-label t headL) (sym (++-assoc pre37 flatTxt (instr-ctrl (c-label headL) ∷ post))))
                     (trans (label-resolves (pre37 ++ flatTxt) headL post nl)
                            (cong just (+-identityʳ (37 + length flatTxt))))

    -- the loop's exit
    exit-label : find-label prog exitL ≡ just (26 + Y)
    exit-label = resolve pre26 _ exitL refl
      (nl-PRE exitL pre26 (nl-flat exitL (inj₂ l2≤3) (inj₁ l3<4))
        (nl-row exitL (λ e → lt-ne (+-monoʳ-< l1 (s≤s (s≤s (s≤s z≤n)))) e) ∷ᴬ
         (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ)
        (nl-out rbTxt L-rb exitL (inj₁ (<-≤-trans l3<4 (m≤m+n (l1 + 4) (lsize G)))))
        (++⁺ (nl-call exitL) (++⁺ (nl-push exitL) ((λ ()) ∷ᴬ []ᴬ))))

    -- the jump over the body lands on its end label
    end-label : find-label prog endL ≡ just ((33 + length at) + Y)
    end-label =
      trans (resolve Wend [] endL (cong (pre32 ++_) (sym (++-assoc at (instr-ctrl (c-ret bb) ∷ []) (instr-ctrl (c-label endL) ∷ []))))
               (nl-PRE endL Wend (nl-flat endL (inj₂ (≤-trans l2≤4 (≤-trans up4 bl1)))
                                                 (inj₂ (≤-trans (m≤m+n lr (lsize G)) bl1)))
                                 (nl-out hd8 L-hd8 endL (inj₂ (≤-trans up4 bl1)))
                                 (nl-out rbTxt L-rb endL (inj₂ bl1))
                                 (++⁺ (nl-pre32 endL (lt-ne (<-≤-trans l3<4 (≤-trans up4 bl1))))
                                      (++⁺ (nl-out at L-at endL (inj₂ (≤-trans (m≤m+n l1 4) (≤-trans up4 bl1))))
                                           ((λ ()) ∷ᴬ []ᴬ)))))
            (cong (λ z → just (z + Y)) (trans (cong (32 +_) (length-++ at {instr-ctrl (c-ret bb) ∷ []})) (len-e (length at))))
      where
        Wend : AbstractTrace
        Wend = pre32 ++ (at ++ (instr-ctrl (c-ret bb) ∷ []))

    -- the rebuild walk's own labels
    rb-labels : LabelsAt prog (8 + X) rbTxt
    rb-labels m j h =
      trans (la m _ (trans (cong (λ t → find-label t m) eq)
                           (find-label-distrib (pre37 ++ (flatTxt ++ hd8)) rbTxt (mov-to-input ∷ tailTxt) m j nl h)))
            (cong just (trans (cong (λ z → (j + (37 + z)) + base) (length-++ flatTxt {hd8})) (pos-rb j (length flatTxt) base)))
      where
        win = found-in-window rbTxt m j h L-rb
        lo : lr ≤ idx m
        lo = proj₁ win
        nl : NoLabel m (pre37 ++ (flatTxt ++ hd8))
        nl = ++⁺ (nl-pre37 m)
               (++⁺ (nl-flat m (inj₂ (≤-trans l2≤4 (≤-trans (m≤m+n (l1 + 4) (lsize G)) lo))) (inj₂ lo))
                    (nl-out hd8 L-hd8 m (inj₂ (≤-trans (m≤m+n (l1 + 4) (lsize G)) lo))))
        eq : text′ ≡ (pre37 ++ (flatTxt ++ hd8)) ++ (rbTxt ++ (mov-to-input ∷ tailTxt))
        eq = trans (cong (λ t → pre37 ++ (flatTxt ++ t)) R-eq) (cong (pre37 ++_) (sym (++-assoc flatTxt hd8 _)))

    -- the algebra's own labels
    body-labels : LabelsAt prog (32 + Y) at
    body-labels m j h =
      trans (la m _ (trans (cong (λ t → find-label t m) (cut pre32 (at ++ post2) refl))
                           (find-label-distrib (PRE pre32) at post2 m j nl h)))
            (cong just (trans (+-assoc j (length (PRE pre32)) base) (cong (j +_) (pre-pc pre32))))
      where
        win = found-in-window at m j h L-at
        hi : idx m < l1
        hi = proj₂ win
        nl : NoLabel m (PRE pre32)
        nl = nl-PRE m pre32 (nl-flat m (inj₁ hi) (inj₁ (<-≤-trans hi (m≤m+n l1 4))))
                            (nl-out hd8 L-hd8 m (inj₁ (<-≤-trans hi l≤2)))
                            (nl-out rbTxt L-rb m (inj₁ (<-≤-trans hi (≤-trans (m≤m+n l1 4) (m≤m+n (l1 + 4) (lsize G))))))
                            (nl-pre32 m (λ e → lt-ne (<-≤-trans hi (m≤m+n l1 3)) (sym e)))
