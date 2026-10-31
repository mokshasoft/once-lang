-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Flatten   (plan 0.125 S3, cata M4 stage C)
--
-- THE FLATTEN LOOP, run to its exit: from the loop head `ℓ l1` with todo
-- `ts` and eval `es`, the machine reaches the row after the exit label
-- `ℓ (l1+1)` with todo `[]` and eval `FI ts es` — stage A's flatten
-- invariant (`CataBr.Meaning.PO.FI`), silently, as one `Walk`.
--
-- By induction on stage A's measure `length (FI ts [])`, which one round
-- drops by exactly one (`flatten-measure`): a round (`Round.round`) pops
-- `t`, pushes it onto eval and its children onto todo — the machine's
-- children (`kidsI` of the node's top layer) are stage A's (`children-eq`,
-- `pushAll-eq`), and the invariant is kept (`flatten-step`); the empty todo
-- exits (`Exit.out`, `FI [] es = es`).
--
-- The loop keeps the value stack's slot and every slot from the call slots
-- on (`KL`), and everything below the frontier (`Walk.seg`): `keep-val`
-- and `keep-slot` read the value stack and the call slots back at the exit.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Flatten (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Meaning o using (μ-layer-val)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning using (module PO)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Layer o using (kidsI; pushAllV; children-eq; pushAll-eq)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module Pieces)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Round o tbl using (module CataRoundC)
open import Once.CCC.Codegen.IRToTrace o using (fsize)
open import Once.CCC.Machine.SMCore using (AbstractTrace; AllocState; module AllocState; module LocState)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⌈_⌉F; μ-type)
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Spec.Word using (Carrier)
open import Once.Internal.Value Carrier Carrier using (⟦_⟧F)
open import Once.Internal.Iterative using (T∞)
open import Data.Nat using (_*_)
open import Data.Nat.Properties using (suc-injective)

module CataFlattenC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (Kp)
  open CataStackC {FS}
  open CataWalkC {FS}
  open CataRoundC {FS}
  open LocState using (halted)
  open AllocState using (current-frame)

  -- what a walk keeping `KL` leaves of the value stack and of a call slot
  module Keep {prog n K σ e Q} (w : Walk prog n K σ e Q) where
    τ = Walk.τ w

    keep-stack : ∀ {V : Set} {E : ElemP V} → ETr E → ∀ {k sn xs} → K k
               → StackAt E (falloc σ) (floc σ) k sn xs → StackAt E (falloc τ) (floc τ) k sn xs
    keep-stack et {k} kk st = stack-keep et (walk-kp w) (Walk.cf w) (Walk.slots w k kk) st

    keep-slot : ∀ {k v} → K k
              → readLoc (floc σ) (AtStack (current-frame (falloc σ)) k) ≡ just v
              → readLoc (floc τ) (AtStack (current-frame (falloc τ)) k) ≡ just v
    keep-slot {k} kk r = trans (cong (λ f → readLoc (floc τ) (AtStack f k)) (Walk.cf w)) (trans (Walk.slots w k kk) r)

    keep-heap : ∀ {l v} → Live (falloc σ) l → readLoc (floc σ) l ≡ just v → readLoc (floc τ) l ≡ just v
    keep-heap lv r = trans (proj₂ (walk-kp w) _ lv) r

  module Flatten (prog : AbstractTrace) {F : IRFunctor} (wf : WellFormedFI F)
                 {C₀ : Set} (alg₀ : ⟦ ⌈ F ⌉F ⟧F C₀ → T∞ C₀)
                 (n c l1 : ℕ) (sn : HeapLocation)
                 (cb : n + 7 + 4 * fsize ⌈ F ⌉F ≤ c) (H : ℕ)
                 (span : SpanAt prog H (Pieces.flatTxt ⌈ F ⌉F n l1))
                 (hd : find-label prog (ℓ o l1) ≡ just H)
                 (ex : find-label prog (ℓ o (suc l1)) ≡ just ((23 + length (Pieces.visitTxt ⌈ F ⌉F n l1)) + H))
                 (lv : LabelsAt prog (22 + H) (Pieces.visitTxt ⌈ F ⌉F n l1)) where

    module L = Loop prog wf n c l1 sn cb H span hd ex lv
    open L
    module P = PO (wf-⌈⌉ wf) alg₀

    -- the loop's exit: todo empty, eval the invariant
    FQ : List ⟦ μ-type F ⟧ → List ⟦ μ-type F ⟧ → FlatState → Set
    FQ ts es = EQ [] (P.FI ts es)

    flatten : ∀ (m : ℕ) (σ : FlatState) (ts es : List ⟦ μ-type F ⟧) → length (P.FI ts []) ≡ m
            → fpc σ ≡ H → halted (floc σ) ≡ false
            → StackAt NE (falloc σ) (floc σ) n sn ts → StackAt NE (falloc σ) (floc σ) (suc n) sn es
            → Walk prog n K σ (suc XL) (FQ ts es)
    flatten zero    σ []       es eq pcH nh st se = Exit.out σ es pcH nh st se
    flatten (suc m) σ []       es eq pcH nh st se = Exit.out σ es pcH nh st se
    flatten zero    σ (t ∷ ts) es eq pcH nh st se = ⊥-elim (no0 (trans (P.flatten-measure t ts) eq))
      where no0 : ∀ {k : ℕ} → suc k ≡ 0 → ⊥
            no0 ()
    flatten (suc m) σ (t ∷ ts) es eq pcH nh st se = walk-∘ {prog} {n} {K} {σ} r (walk-post rest done)
      where
        r = Round.round σ t ts es pcH nh st se
        τ = Walk.τ r
        ks = P.pushAll (P.children t) ts

        eqk : pushAllV (kidsI wf (μ-type F) (μ-layer-val wf t)) ts ≡ ks
        eqk = trans (cong (λ z → pushAllV z ts) (children-eq wf alg₀ t))
                    (sym (pushAll-eq (wf-⌈⌉ wf) alg₀ (P.children t) ts))

        st′ : StackAt NE (falloc τ) (floc τ) n sn ks
        st′ = subst (StackAt NE (falloc τ) (floc τ) n sn) eqk (proj₁ (Walk.post r))

        rest : Walk prog n K τ (suc XL) (FQ ks (t ∷ es))
        rest = flatten m τ ks (t ∷ es) (suc-injective (trans (P.flatten-measure t ts) eq)) (Walk.pc r) (Walk.nh r)
                 st′ (proj₂ (Walk.post r))

        done : FQ (t ∷ ts) es (Walk.τ rest)
        done = proj₁ (Walk.post rest)
             , subst (StackAt NE (falloc (Walk.τ rest)) (floc (Walk.τ rest)) (suc n) sn) (P.flatten-step t ts es)
                     (proj₂ (Walk.post rest))

    -- from the root: todo `[ root ]`, eval `[]`
    abstract
      flatten-root : ∀ (σ : FlatState) (root : ⟦ μ-type F ⟧) → fpc σ ≡ H → halted (floc σ) ≡ false
                   → StackAt NE (falloc σ) (floc σ) n sn (root ∷ []) → StackAt NE (falloc σ) (floc σ) (suc n) sn []
                   → Walk prog n K σ (suc XL) (FQ (root ∷ []) [])
      flatten-root σ root pcH nh st se = flatten _ σ (root ∷ []) [] refl pcH nh st se
