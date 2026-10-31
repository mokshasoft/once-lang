-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterRun
--
-- plan 0.119 D5: the loop's RUN SCAFFOLDING — where every row sits and how
-- long the text is (`CaseRun`'s counterpart). Offsets past the round are
-- written `(3 + length bt) + j`: the round ends there (`at-end` of the
-- round's own witness, emitted at `3 + base`), and the post rows follow.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterRun (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.SMCore
  using (instr-ctrl; c-branch-tag-zero; c-jmp; c-label; AbstractTrace; AbstractInstr;
         load-indirect; load-indirect-suc; store-at-slot; instr-alloc-heap; mov-to-input;
         load-from-slot; store-indirect; store-indirect-suc)
open import Once.IRTy using (IRTy)
import Once.IRTy as IRT

open import Once.CCC.Codegen.IRObsCorrect.IterShape o tbl

module IterRunC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open IterShapeC {FS}

  module IterRun {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A))
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (Iter body)))
    where

    open IterShape body n l

    -- The emitted length: the prologue, the round, the sixteen post rows.
    len-eq : length (emitted n l (Iter body)) ≡ 3 + (length bt + 16)
    len-eq = trans (length-++ pre {bt ++ post}) (cong (3 +_) (length-++ bt {post}))

    -- Where the round ends, and where the loop ends.
    rend : ℕ
    rend = 3 + length bt

    end-eq : length (emitted n l (Iter body)) + base ≡ (rend + 16) + base
    end-eq = cong (_+ base) (trans len-eq (sym (+-assoc 3 (length bt) 16)))

    -- The round's own end pc, as its witness states it (`at-end` at `3 + base`),
    -- is the first post row's.
    rend-eq : length bt + suc (suc (suc base)) ≡ (rend + 0) + base
    rend-eq = trans (sym (+-assoc (length bt) 3 base))
                    (cong (_+ base) (trans (+-comm (length bt) 3) (sym (+-identityʳ (3 + length bt)))))

    ------------------------------------------------------------------
    -- THE FETCHES.
    ------------------------------------------------------------------
    at-load : fetch prog (0 + base) ≡ just load-indirect
    at-load = span 0 _ refl

    at-store : fetch prog (1 + base) ≡ just (store-at-slot (suc n))
    at-store = span 1 _ refl

    at-top : fetch prog (2 + base) ≡ just (instr-ctrl (c-label (ℓ o l)))
    at-top = span 2 _ refl

    post-at : ∀ (j : ℕ) (i : AbstractInstr)
            → fetch post j ≡ just i
            → fetch prog ((rend + j) + base) ≡ just i
    post-at j i e =
      subst (λ z → fetch prog (z + base) ≡ just i)
            (trans (cong (3 +_) (+-comm j (length bt))) (sym (+-assoc 3 (length bt) j)))
            (span (3 + (j + length bt)) i
              (subst (λ z → fetch (bt ++ post) z ≡ just i)
                     (+-comm (length bt) j)
                     (trans (fetch-++-right bt post j) e)))

    at-movin1 : fetch prog ((rend + 0) + base) ≡ just mov-to-input
    at-movin1 = post-at 0 _ refl
    at-branch : fetch prog ((rend + 1) + base) ≡ just (instr-ctrl (c-branch-tag-zero (ℓ o (suc l))))
    at-branch = post-at 1 _ refl
    at-unpack : fetch prog ((rend + 2) + base) ≡ just load-indirect-suc
    at-unpack = post-at 2 _ refl
    at-movin2 : fetch prog ((rend + 12) + base) ≡ just mov-to-input
    at-movin2 = post-at 12 _ refl
    at-jmp : fetch prog ((rend + 13) + base) ≡ just (instr-ctrl (c-jmp (ℓ o l)))
    at-jmp = post-at 13 _ refl
    at-done : fetch prog (done-at + base) ≡ just (instr-ctrl (c-label (ℓ o (suc l))))
    at-done = post-at 14 _ refl
    at-out : fetch prog ((rend + 15) + base) ≡ just load-indirect-suc
    at-out = post-at 15 _ refl

    -- the nine tail rows, `3 ≤ j ≤ 11`
    at-tail : ∀ (j : ℕ) (i : AbstractInstr) → fetch post (3 + j) ≡ just i
            → fetch prog ((rend + (3 + j)) + base) ≡ just i
    at-tail j i e = post-at (3 + j) i e

    ------------------------------------------------------------------
    -- D158's hand-over, restated locally (as `CaseRun` does).
    ------------------------------------------------------------------
    handover-eq : ∀ (b : ℕ) (fs : FlatState) (rs : List ℕ)
                → fpc fs ≡ b → fret fs ≡ rs → flink fs ≡ nothing
                → fs ≡ entry-flat b (floc fs) (falloc fs) (fclosure fs) rs
    handover-eq b (mkFlatFull lo al pc rt cls lk) _ refl refl refl = refl
