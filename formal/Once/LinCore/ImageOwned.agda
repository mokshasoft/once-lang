-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageOwned — plan 0.146 B1.7 step 3 (D462): ★ EVERY OP CALL
-- OF THE NEW IMAGE NAMES ONE OF ITS BLOCKS.
--
-- The image's blocks are its ops' (`ImageBlocks.imageBlocks`, which the
-- emitter writes into the file: `Emit.blocksOf`). The image calls an op
-- as `lowOp` lowers it: itself, or a comparison's block (`opSig`,
-- `ImageAll.sigops`). A canonical op (`AsBlock.Canonical`: a block named by
-- its digest, a primitive a comparison) is then master's `Named`: the call
-- names a block of the image's, whose body is its contract (`BlockOf`) —
-- what the arch layer's arith table reads (master's `RewriteOwned`, here by
-- construction of the bridge's ops).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Data.Nat using (ℕ)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.ImageOwned (fmt : TargetNum) (bw : Base → ℕ) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Once.Spec.Name using (CanonicalName)
import Once.Spec.Type as ST
open import Once.SigOp.Info using (SigOpInfo; SigOpSem; mk-info'; blockV; primV; ffiV; callsV; emitsV; haltsV; module SigOpInfo)
open import Once.Arith.Prim using (p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; p-fneg; p-cmp; p-fcmp)
open import Once.Arith.CmpOp using (fcmp)
open import Once.Arith.Machine.IR using (ArithBlock; mk-block)
open import Once.Arith.Machine.Rewrite using (sigop-blocks)
open import Once.Arith.SigOp.Compare using (cmp-of; cmp-block; cmp-body; int-c; flt-c)
open import Once.Arith.SigOp.AsBlock using (CanonicalAt; Canonical)
open import Once.Adequacy.RewriteOwned using (Named; BlockOf; is-block)
open import Once.LinCore.Core fmt using (Sig; sig; info)
open import Once.LinCore.Lower fmt bw using (cmpOf; opSig)
open import Once.LinCore.Keys fmt bw using (Univ; ops)

open import Once.LinCore.ImageBlocks fmt bw using (own; opBlks; imageBlocks; op-blocks)

------------------------------------------------------------------------
-- ★ A canonical op's call names a block of any list holding its blocks.
------------------------------------------------------------------------

private
  named-at : ∀ (bs : List ArithBlock) {A B} nm (sm : SigOpSem A B) (bA : ST.Base ST.∅ₖ A) (cB : ST.Base ST.∅ₖ B)
           → CanonicalAt nm sm → (∀ {b} → b ∈ own sm ++ sigop-blocks (cmp-of sm) → b ∈ bs)
           → Named bs (info (opSig (sig (mk-info' nm sm bA cB)) (cmp-of sm)))
  named-at bs nm (blockV {sh} {n} e eA eB) bA cB c sub _ = mk-block sh n e , sub (here refl) , c , is-block e eA eB refl
  named-at bs nm (primV p-add)  bA cB () sub
  named-at bs nm (primV p-sub)  bA cB () sub
  named-at bs nm (primV p-mul)  bA cB () sub
  named-at bs nm (primV p-div)  bA cB () sub
  named-at bs nm (primV p-mod)  bA cB () sub
  named-at bs nm (primV p-neg)  bA cB () sub
  named-at bs nm (primV p-fadd) bA cB () sub
  named-at bs nm (primV p-fsub) bA cB () sub
  named-at bs nm (primV p-fmul) bA cB () sub
  named-at bs nm (primV p-fdiv) bA cB () sub
  named-at bs nm (primV p-i2f)  bA cB () sub
  named-at bs nm (primV p-fneg) bA cB () sub
  named-at bs nm (primV (p-cmp o))    bA cB c sub _ =
    cmp-block (int-c o) , sub (here refl) , refl , is-block (cmp-body (int-c o)) refl refl refl
  named-at bs nm (primV (p-fcmp h o)) bA cB c sub _ =
    cmp-block (flt-c (fcmp h o)) , sub (here refl) , refl , is-block (cmp-body (flt-c (fcmp h o))) refl refl refl
  named-at bs nm ffiV       bA cB c sub ()
  named-at bs nm callsV     bA cB c sub ()
  named-at bs nm (emitsV _) bA cB c sub ()
  named-at bs nm (haltsV _) bA cB c sub ()

named-op : ∀ (bs : List ArithBlock) (s : Sig) → Canonical (info s) → (∀ {b} → b ∈ opBlks s → b ∈ bs)
         → Named bs (info (opSig s (cmpOf s)))
named-op bs s c sub =
  named-at bs (SigOpInfo.name (info s)) (SigOpInfo.sem (info s)) (SigOpInfo.baseA (info s)) (SigOpInfo.conB (info s)) c sub

-- ★★ a call the image makes (`ImageAll.sigops`: an op of the universe's,
-- lowered), its op canonical, names a block of the image's
named-call : ∀ (U : Univ) (canon : ∀ {s} → s ∈ ops U → Canonical (info s))
           → ∀ {A B} (si : SigOpInfo A B) → Σ Sig (λ s → s ∈ ops U × sig si ≡ opSig s (cmpOf s))
           → Named (imageBlocks U) si
named-call U canon si (s , p , e) =
  subst (λ t → Named (imageBlocks U) (info t)) (sym e) (named-op (imageBlocks U) s (canon p) (op-blocks p))
