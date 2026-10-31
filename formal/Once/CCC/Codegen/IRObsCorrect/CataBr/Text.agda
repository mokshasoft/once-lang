-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Text   (plan 0.135 S3, cata M4 stage C)
--
-- WHERE THE PARTS OF A `strat-branching` CATA SIT. Its text
-- (`cata-trace-branching`) is
--
--     setup (13) ++ init (14) ++ push2 root (10)            the first 37 rows
--       ++ FLATTEN                                          rows 37 …
--       ++ fold prefix ++ call ++ I₂ ++ body                the rest (`R`)
--
-- with the FLATTEN loop (`flatTxt`)
--
--     ℓ l1:  load todo · mov-to-input · branch-tag-zero (ℓ (l1+1))     the head (10
--            load-indirect-suc · store todo · load-indirect ·            rows, `headTxt`)
--            mov-to-input · store tmp · load tmp
--            push2 eval                                               10 rows
--            load tmp · mov-to-input                                   2 rows
--            visit-walk F (n+7) (l1+4)                                `visitTxt`
--            c-jmp ℓ l1 · ℓ (l1+1):                                    `exitTxt`
--
-- The cata's slots: todo n, eval n+1, val n+2, tmp n+3, push scratch n+4/5,
-- sentinel n+6, walk slots from n+7, and the call's four slots from
-- `cslot = n+7+4·fsize F+4` on (cl, k, ev, pr).
--
-- This module reads the cata's placement premises down to what stage C's
-- runs need: the spans of the setup, the init and the flatten fragment, the
-- loop head's and the exit's label resolution, and the visit walk's own
-- `LabelsAt` (the loop's only labels are `ℓ l1` and `ℓ (l1+1)`, and the
-- walk's window starts at `l1+4`). The emitted text is matched once, by
-- `emitted-eq` (the classifier's `strat-branching` carries `⌈ F ⌉F`
-- itself, `br-fun`) and `text-eq` (two `++-assoc` around the visit walk,
-- the only non-literal piece before the fold).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Text (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRToTrace o
  using (rec-count; cata-strategy; CataStrategy; strat-const; strat-branching; cata-dispatch; cata-trace-branching
        ; cata-call-setup; cata-call; cata-body; cata-br-I₂; push2; visit-walk; rebuild-walk; fsize; lsize)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (visit-ls)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; instr-ctrl; c-jmp; c-label; c-branch-tag-zero; load-from-slot; store-at-slot; mov-to-input; mov-to-output
        ; load-indirect; load-indirect-suc; store-indirect; instr-alloc-heap; instr-load-tag-lit)
open import Once.CCC.Label using (ℓ; LabelId; module LabelId)
open LabelId using (idx)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F)
open import Once.Spec.Type using (Fun)
import Once.IRTy as IRTy′
import Data.Nat as ℕ
open import Data.Nat using (s≤s; z≤n)
open import Data.Nat.Properties using (+-monoʳ-<; +-cancelˡ-≡)
open import Data.Maybe using () renaming (map to mmapT)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

-- the classifier's `strat-branching` carries the functor it classified
br-fun : ∀ (G : Fun 0) {H : Fun 0} → cata-strategy G ≡ strat-branching H → H ≡ G
br-fun G eq with rec-count G | eq
... | zero  | ()
... | suc _ | refl = refl

------------------------------------------------------------------------
-- THE INIT ROWS (`cata-br-I₁`'s first fourteen): stash the root at tmp,
-- allocate the sentinel `[SV-Tag 0 , _]` at n+6, point eval, val and todo
-- at it, the root back into `Output`.
------------------------------------------------------------------------
init-rows : ℕ → AbstractTrace
init-rows n =
  mov-to-output ∷ store-at-slot (n ℕ.+ 3) ∷
  instr-alloc-heap 2 ∷ store-at-slot (n ℕ.+ 6) ∷ mov-to-input ∷
  instr-load-tag-lit 0 ∷ store-indirect ∷
  load-from-slot (n ℕ.+ 6) ∷ store-at-slot (suc n) ∷
  load-from-slot (n ℕ.+ 6) ∷ store-at-slot (n ℕ.+ 2) ∷
  load-from-slot (n ℕ.+ 6) ∷ store-at-slot n ∷
  load-from-slot (n ℕ.+ 3) ∷ []

------------------------------------------------------------------------
-- THE SLOTS BELOW THE CALL SLOTS: everything the init and the flatten loop
-- write (n … n+6, and the walk slots) is below `c ≥ n+7`, so a slot from
-- `c` on is none of them (`far`).
------------------------------------------------------------------------
module SlotArith (n c : ℕ) (n7≤c : n ℕ.+ 7 ≤ c) where
  private
    q : ∀ (d : ℕ) → d < 7 → n ℕ.+ d < c
    q d d<7 = <-≤-trans (+-monoʳ-< n d<7) n7≤c

  lt0 : n < c
  lt0 = subst (_< c) (+-identityʳ n) (q 0 (s≤s z≤n))
  lt1 : suc n < c
  lt1 = subst (_< c) (trans (+-suc n 0) (cong suc (+-identityʳ n))) (q 1 (s≤s (s≤s z≤n)))
  lt2 : n ℕ.+ 2 < c
  lt2 = q 2 (s≤s (s≤s (s≤s z≤n)))
  lt3 : n ℕ.+ 3 < c
  lt3 = q 3 (s≤s (s≤s (s≤s (s≤s z≤n))))
  lt4 : n ℕ.+ 4 < c
  lt4 = q 4 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
  lt5 : n ℕ.+ 5 < c
  lt5 = q 5 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
  lt6 : n ℕ.+ 6 < c
  lt6 = q 6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

  far : ∀ {j k : ℕ} → k < c → c ≤ j → j ≢ k
  far k<c c≤j refl = <-irrefl refl (<-≤-trans k<c c≤j)

-- distinct offsets above one base are distinct slots
module OffArith (n : ℕ) where
  off-≢ : ∀ {a b : ℕ} → a ≢ b → n ℕ.+ a ≢ n ℕ.+ b
  off-≢ ne e = ne (+-cancelˡ-≡ n _ _ e)

  off0-≢ : ∀ {b : ℕ} → 0 ≢ b → n ≢ n ℕ.+ b
  off0-≢ ne e = ne (+-cancelˡ-≡ n _ _ (trans (+-identityʳ n) e))

  suc-is : suc n ≡ n ℕ.+ 1
  suc-is = sym (trans (+-suc n 0) (cong suc (+-identityʳ n)))

  -- the slots the flatten loop and the init name, pairwise
  n≢4 : n ≢ n ℕ.+ 4
  n≢4 = off0-≢ (λ ())
  n≢5 : n ≢ n ℕ.+ 5
  n≢5 = off0-≢ (λ ())
  4≢5 : n ℕ.+ 4 ≢ n ℕ.+ 5
  4≢5 = off-≢ (λ ())
  s≢4 : suc n ≢ n ℕ.+ 4
  s≢4 e = off-≢ {1} {4} (λ ()) (trans (sym suc-is) e)
  s≢5 : suc n ≢ n ℕ.+ 5
  s≢5 e = off-≢ {1} {5} (λ ()) (trans (sym suc-is) e)
  s≢n : suc n ≢ n
  s≢n e = <-irrefl (sym e) (n<1+n n)

------------------------------------------------------------------------
-- THE PIECES, as the emitter writes them (`cata-br-I₁`), for a functor `G`,
-- slot base `n` and label base `l1`.
------------------------------------------------------------------------
module Pieces (G : Fun 0) (n l1 : ℕ) where

  cslot bodyL : ℕ
  cslot = n ℕ.+ 7 ℕ.+ (4 ℕ.* fsize G) ℕ.+ 4
  bodyL = l1 ℕ.+ 4 ℕ.+ lsize G ℕ.+ lsize G

  setupTxt initTxt rootTxt headTxt pushTxt reloadTxt visitTxt exitTxt foldTxt flatTxt : AbstractTrace
  setupTxt = cata-call-setup cslot (cslot ℕ.+ 1) (cslot ℕ.+ 2) bodyL
  initTxt = init-rows n
  rootTxt = push2 n (n ℕ.+ 4) (n ℕ.+ 5)
  headTxt =
    instr-ctrl (c-label (ℓ o l1)) ∷
    load-from-slot n ∷ mov-to-input ∷
    instr-ctrl (c-branch-tag-zero (ℓ o (suc l1))) ∷
    load-indirect-suc ∷ store-at-slot n ∷
    load-indirect ∷ mov-to-input ∷ store-at-slot (n ℕ.+ 3) ∷
    load-from-slot (n ℕ.+ 3) ∷ []
  pushTxt = push2 (suc n) (n ℕ.+ 4) (n ℕ.+ 5)
  reloadTxt = load-from-slot (n ℕ.+ 3) ∷ mov-to-input ∷ []
  visitTxt = visit-walk n (n ℕ.+ 4) (n ℕ.+ 5) G (n ℕ.+ 7) (l1 ℕ.+ 4)
  exitTxt = instr-ctrl (c-jmp (ℓ o l1)) ∷ instr-ctrl (c-label (ℓ o (suc l1))) ∷ []
  foldTxt =
    (instr-ctrl (c-label (ℓ o (l1 ℕ.+ 2))) ∷
     load-from-slot (suc n) ∷ mov-to-input ∷
     instr-ctrl (c-branch-tag-zero (ℓ o (l1 ℕ.+ 3))) ∷
     load-indirect-suc ∷ store-at-slot (suc n) ∷
     load-indirect ∷ mov-to-input ∷ []) ++
    rebuild-walk (n ℕ.+ 2) (n ℕ.+ 4) (n ℕ.+ 5) G (n ℕ.+ 7) (l1 ℕ.+ 4 ℕ.+ lsize G) ++
    (mov-to-input ∷ [])

  -- the flatten loop, head label to exit label
  flatTxt = headTxt ++ (pushTxt ++ (reloadTxt ++ (visitTxt ++ exitTxt)))

  -- the first 37 rows (all literal)
  pre37 : AbstractTrace
  pre37 = setupTxt ++ (initTxt ++ rootTxt)

  -- what follows the flatten loop, given what follows `cata-br-I₁`
  restTxt : AbstractTrace → AbstractTrace
  restTxt Y = foldTxt ++ Y

------------------------------------------------------------------------
-- THE TEXT OF ONE CATA, and its two readings.
------------------------------------------------------------------------
module CataBrTextC {FS : FrameSemantics} where

  open Core {FS}
  open ResuspBaseC {FS} using (span-take; span-drop)
  open Resolve {FS} using (NoLabel; noLabel-outside; fl-hit; found-in-window)
  open FlatStepsAPI {FS} using (fl-go-skip; fl-go-shift; fl-go-prefix)

  module Text {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C) (n l : ℕ) where

    bb l1 : ℕ
    bb = proj₁ (ir-to-trace' 0 l alg)
    l1 = proj₁ (proj₂ (ir-to-trace' 0 l alg))

    at : AbstractTrace
    at = emitted 0 l alg

    G : Fun 0
    G = ⌈ F ⌉F

    module Pc = Pieces G n l1
    open Pc

    -- what follows `cata-br-I₁`: the call, `I₂`, the body
    tailTxt : AbstractTrace
    tailTxt = cata-call cslot (cslot ℕ.+ 1) (cslot ℕ.+ 2) (cslot ℕ.+ 3) ++ (cata-br-I₂ n l1 ++ cata-body bodyL (bodyL ℕ.+ 1) bb at)

    R : AbstractTrace
    R = restTxt tailTxt

    text : AbstractTrace
    text = proj₂ (proj₂ (cata-trace-branching G bb n l1 at))

    -- the same text, cut at the flatten loop
    text′ : AbstractTrace
    text′ = pre37 ++ (flatTxt ++ R)

    text-eq : text ≡ text′
    text-eq = cong (λ z → setupTxt ++ (initTxt ++ (rootTxt ++ (headTxt ++ (pushTxt ++ (reloadTxt ++ z))))))
                   (trans (++-assoc visitTxt (exitTxt ++ foldTxt) tailTxt)
                          (sym (++-assoc visitTxt exitTxt (foldTxt ++ tailTxt))))

    -- `ir-to-trace'`'s dispatch, at the strategy this case is about
    emitted-eq : ∀ {H : Fun 0} → cata-strategy ⌈ F ⌉F ≡ strat-branching H → emitted n l (Cata wf alg) ≡ text′
    emitted-eq {H} eq = trans e₁ (trans e₂ text-eq)
      where
        e₁ : emitted n l (Cata wf alg) ≡ proj₂ (proj₂ (cata-trace-branching H bb n l1 at))
        e₁ = cong (λ st → proj₂ (proj₂ (cata-dispatch st bb n l1 at))) eq
        e₂ : proj₂ (proj₂ (cata-trace-branching H bb n l1 at)) ≡ text
        e₂ = cong (λ K → proj₂ (proj₂ (cata-trace-branching K bb n l1 at))) {H} {G} (br-fun G eq)

    ------------------------------------------------------------------
    -- LABELS: the loop's two, and the visit walk's window.
    ------------------------------------------------------------------
    private
      idx-of : Maybe LabelId → ℕ
      idx-of (just m) = idx m
      idx-of nothing  = 0

      -- the 22 rows before the visit walk define only `ℓ l1`
      nl-pre : ∀ (m : LabelId) → idx m ≢ l1 → NoLabel m (headTxt ++ (pushTxt ++ reloadTxt))
      nl-pre m ne =
        (λ e → ne (sym (cong idx-of e))) ∷ᴬ
        (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ
        (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ
        (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      lt4 : ∀ (k : ℕ) → suc k < k ℕ.+ 4
      lt4 k = subst (suc k <_) (+-comm 4 k) (s≤s (s≤s (m≤n+m k 2)))

      sl1≢l1 : suc l1 ≢ l1
      sl1≢l1 e = <-irrefl (sym e) (n<1+n l1)

      vls = visit-ls G n (n ℕ.+ 4) (n ℕ.+ 5) (n ℕ.+ 7) (l1 ℕ.+ 4)

      -- the exit label is below the walk's window
      nl-visit-exit : NoLabel (ℓ o (suc l1)) visitTxt
      nl-visit-exit = noLabel-outside (ℓ o (suc l1)) visitTxt vls (λ w → <-irrefl refl (<-≤-trans (lt4 l1) (proj₁ w)))

    head-scan : find-label text′ (ℓ o l1) ≡ just 37
    head-scan = fl-hit (ℓ o l1) _ 37

    exit-scan : find-label text′ (ℓ o (suc l1)) ≡ just (suc (59 ℕ.+ length visitTxt))
    exit-scan =
      trans (fl-go-skip (headTxt ++ (pushTxt ++ reloadTxt)) ((visitTxt ++ exitTxt) ++ R) (ℓ o (suc l1)) 37 (nl-pre (ℓ o (suc l1)) sl1≢l1))
      (trans (cong (λ t → fl-go t (ℓ o (suc l1)) 59) (++-assoc visitTxt exitTxt R))
      (trans (fl-go-skip visitTxt (exitTxt ++ R) (ℓ o (suc l1)) 59 nl-visit-exit)
             (fl-hit (ℓ o (suc l1)) R (suc (59 ℕ.+ length visitTxt)))))

    -- a label the visit walk resolves, the cata resolves 59 rows on
    visit-scan : ∀ (m : LabelId) (j : ℕ) → find-label visitTxt m ≡ just j → find-label text′ m ≡ just (j ℕ.+ 59)
    visit-scan m j eq =
      trans (fl-go-skip (headTxt ++ (pushTxt ++ reloadTxt)) ((visitTxt ++ exitTxt) ++ R) m 37 (nl-pre m ne))
      (trans (cong (λ t → fl-go t m 59) (++-assoc visitTxt exitTxt R))
      (trans (fl-go-shift (visitTxt ++ (exitTxt ++ R)) m 59 0)
             (cong (mmapT (ℕ._+ 59)) (fl-go-prefix visitTxt (exitTxt ++ R) m 0 j eq))))
      where
        win = found-in-window visitTxt m j eq vls
        ne : idx m ≢ l1
        ne e = <-irrefl refl (<-≤-trans (<-trans (n<1+n l1) (lt4 l1)) (subst (l1 ℕ.+ 4 ≤_) e (proj₁ win)))

    ------------------------------------------------------------------
    -- …and in the program.
    ------------------------------------------------------------------
    module At (prog : AbstractTrace) (base : ℕ) (span : SpanAt prog base text′) (la : LabelsAt prog base text′) where

      H : ℕ
      H = 37 ℕ.+ base

      span-setup : SpanAt prog base setupTxt
      span-setup = span-take prog setupTxt {initTxt ++ (rootTxt ++ (flatTxt ++ R))} base span

      span-init : SpanAt prog (13 ℕ.+ base) (initTxt ++ rootTxt)
      span-init = span-take prog (initTxt ++ rootTxt) {flatTxt ++ R} (13 ℕ.+ base)
                    (span-drop prog setupTxt {initTxt ++ (rootTxt ++ (flatTxt ++ R))} base span)

      span-flat′ : SpanAt prog H (flatTxt ++ R)
      span-flat′ = span-drop prog pre37 {flatTxt ++ R} base span

      span-flat : SpanAt prog H flatTxt
      span-flat = span-take prog flatTxt {R} H span-flat′

      -- the fold and everything after it
      span-rest : SpanAt prog (length flatTxt ℕ.+ H) R
      span-rest = span-drop prog flatTxt {R} H span-flat′

      head-label : find-label prog (ℓ o l1) ≡ just H
      head-label = la (ℓ o l1) 37 head-scan

      exit-label : find-label prog (ℓ o (suc l1)) ≡ just ((23 ℕ.+ length visitTxt) ℕ.+ H)
      exit-label = trans (la (ℓ o (suc l1)) _ exit-scan) (cong just (pos (length visitTxt) base))
        where
          pos : ∀ (v b : ℕ) → suc (59 ℕ.+ v) ℕ.+ b ≡ (23 ℕ.+ v) ℕ.+ (37 ℕ.+ b)
          pos = solve 2 (λ v b → (con 60 :+ v) :+ b := (con 23 :+ v) :+ (con 37 :+ b)) refl

      visit-labels : LabelsAt prog (22 ℕ.+ H) visitTxt
      visit-labels m j eq = trans (la m (j ℕ.+ 59) (visit-scan m j eq)) (cong just (+-assoc j 59 base))
